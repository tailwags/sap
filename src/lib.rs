#![warn(clippy::pedantic)]
#![warn(clippy::complexity)]
//! # Sap - a Small Argument Parser
//!
//! A minimal Unix command-line argument parser with zero dependencies.
//!
//! ## Features
//!
//! - Parse short options (`-a`, `-b`), long options (`--verbose`), and option values
//! - Combined short options (`-abc` = `-a -b -c`)
//! - Support for option values (`--name=value`)
//! - Error handling with descriptive messages

use std::{
    env,
    error::Error,
    ffi::OsString,
    fmt::{Debug, Display},
    mem,
    os::unix::ffi::{OsStrExt, OsStringExt},
};

/// Result type specific to Sap, using `ParsingError` as the default error type
pub type Result<T, E = ParsingError> = core::result::Result<T, E>;

/// Represents a command-line argument
#[derive(Debug, PartialEq, PartialOrd, Ord, Eq, Hash, Clone, Copy)]
pub enum Argument<'a> {
    /// A long option like `--example`
    Long(&'a str),

    /// A single character option like `-q`
    Short(char),

    /// A positional argument like `file.txt` or `/path/to/file`
    Value(&'a str),
}

impl<'a> Argument<'a> {
    /// Converts this argument into an error, optionally with a value
    pub fn into_error<A>(self, value: A) -> ParsingError
    where
        A: Into<Option<&'a str>>,
    {
        use Argument::{Long, Short, Value};

        match self {
            Long(arg) => ParsingError::UnexpectedArg {
                offender: arg.to_string(),
                value: value.into().map(String::from),
                format: "=",
                prefix: "--",
            },

            Short(arg) => ParsingError::UnexpectedArg {
                offender: arg.to_string(),
                value: value.into().map(String::from),
                format: " ",
                prefix: "-",
            },

            Value(arg) => ParsingError::UnexpectedArg {
                offender: arg.to_string(),
                value: None,
                format: "",
                prefix: "",
            },
        }
    }
}

/// Internal parser state
enum State {
    /// Normal state, no special processing needed
    NotInteresting,
    /// Contains a value from previous option
    LeftoverValue(OsString),
    /// Combined short options state (-abc)
    Combined(usize, OsString),
    /// End of arguments (after --)
    End,
}

/// Parser for command-line arguments
pub struct Parser<I: Iterator> {
    iter: I,
    state: State,

    // TODO: use these two for better errors.
    last_short: Option<char>,
    last_long: Option<OsString>,

    name: String,
}

impl Parser<env::ArgsOs> {
    /// Creates a `Parser` using the program's command-line arguments.
    ///
    /// # Errors
    ///
    /// Returns an error if no arguments are available or the program name
    /// contains invalid UTF-8.
    pub fn from_env() -> Result<Self> {
        Self::from_arbitrary(env::args_os())
    }
}

impl<I> Parser<I>
where
    I: Iterator<Item = OsString>,
{
    /// Creates a `Parser` from any iterator that yields `OsString` items.
    ///
    /// # Errors
    ///
    /// Returns an error if the iterator is empty or the first item (program name)
    /// can't be converted to a valid UTF-8 string.
    pub fn from_arbitrary<A>(iter: A) -> Result<Parser<I>>
    where
        A: IntoIterator<IntoIter = I>,
    {
        let mut iter = iter.into_iter();
        let name = match iter.next() {
            None => {
                let err = ParsingError::Empty;
                return Err(err);
            }
            Some(val) => match val.into_string() {
                Ok(str) => str,
                Err(_) => return Err(ParsingError::InvalidString),
            },
        };

        Ok(Parser {
            iter,
            state: State::NotInteresting,

            last_short: None,
            last_long: None,
            name,
        })
    }

    /// Moves to the next argument, parsing it into an `Argument` enum.
    ///
    /// # Returns
    ///
    /// - `Some(Ok(arg))` - Successfully parsed the next argument
    /// - `Some(Err(e))` - Found an argument but encountered an error parsing it
    /// - `None` - No more arguments or reached `--` separator
    ///
    /// # Errors
    ///
    /// The parser returns an `Err` when the
    /// argument's data was either itself invalid
    /// (malformed UTF-8 for example) or when it was in an
    /// invalid state, such as `-abc=value`
    /// (here it's invalid for multiple short options to take in a value)
    pub fn forward<'a, 'b>(&'a mut self) -> Result<Option<Argument<'b>>>
    where
        'a: 'b,
    {
        if matches!(self.state, State::End) {
            return Ok(None);
        }

        match self.state {
            State::End => return Ok(None),
            State::Combined(ref mut pos, ref str) => match str.as_bytes().get(*pos) {
                None => {
                    self.state = State::NotInteresting;
                    return self.forward();
                }

                Some(b'=') if *pos > 1 => {
                    let err = ParsingError::InvalidOption {
                        reason: "too much characters after the equals sign",
                        offender: None,
                    };

                    return Err(err);
                }

                Some(ch) => {
                    *pos += 1;
                    return Ok(Some(Argument::Short(*ch as char)));
                }
            },

            _ => {}
        }

        let arg = match self.iter.next() {
            None => return Ok(None),
            Some(arg) => {
                self.last_long = Some(arg);
                // Safety:
                //
                // We just placed the value in the variable
                // therefore it cannot be `None`
                // so this `unwrap_unchecked()` is safe.
                unsafe { &self.last_long.as_deref().unwrap_unchecked() }
            }
        };

        if *arg == "--" {
            self.state = State::End;
            return Ok(None);
        }

        let bytes = arg.as_bytes();

        if bytes.first().is_some_and(|x| *x == b'-') {
            // Long option (`--`)
            if bytes.get(1).is_some_and(|x| *x == b'-') {
                let (arg, val) = split_long_opt_value(&arg.as_bytes()[2..]);

                if let Some(val) = val {
                    self.state = State::LeftoverValue(OsString::from_vec(val.to_vec()));
                }

                // might not be needed
                // however the user
                // can be as bright as Proxima Centauri
                // or as dark as Sagittarius A
                let str_arg = match str::from_utf8(arg) {
                    Err(_e) => {
                        let err = ParsingError::InvalidString;
                        return Err(err);
                    }
                    Ok(val) => val,
                };
                Ok(Some(Argument::Long(str_arg)))

            // Short option.
            } else {
                let tmp = bytes.get(1..);

                if let Some(value) = tmp {
                    let char = value[0] as char;

                    if let Some(rest) = value.get(1..) {
                        let new_vec = OsString::from_vec(rest.to_vec());
                        self.state = State::Combined(0, new_vec);
                    }

                    self.last_short = Some(char);
                    Ok(Some(Argument::Short(char)))
                } else {
                    // lonely `-`
                    // probably an error on the user's part
                    // but syntatically correct.
                    Ok(Some(Argument::Value("-")))
                }
            }
        } else {
            // might not be needed,
            // however i am not sure of the user's
            // eternal glory and shine
            let str_arg = match str::from_utf8(arg.as_encoded_bytes()) {
                Err(_e) => {
                    let err = ParsingError::InvalidString;
                    return Err(err);
                }
                Ok(val) => val,
            };

            // lonely value
            Ok(Some(Argument::Value(str_arg)))
        }
    }

    /// Retrieves the value associated with the previous option.
    ///
    /// Returns the raw `OsString` value without UTF-8 conversion.
    ///
    /// # Returns
    ///
    /// - `Some(value)` - The option has a value (e.g., `--name=value`)
    /// - `None` - The option has no value or the value has already been consumed
    pub fn raw_value(&mut self) -> Option<OsString> {
        match self.state {
            State::LeftoverValue(_) => match mem::replace(&mut self.state, State::NotInteresting) {
                State::LeftoverValue(val) => Some(val),
                _ => unreachable!(),
            },

            _ => None,
        }
    }

    /// Retrieves the value associated with the previous option as a UTF-8 string.
    ///
    /// Performs lossy UTF-8 conversion if the value contains invalid UTF-8.
    ///
    /// # Returns
    ///
    /// - `Some(value)` - The option has a value (e.g., `--name=value`)
    /// - `None` - The option has no value or the value has already been consumed
    pub fn value(&mut self) -> Option<String> {
        self.raw_value().map(|v| v.to_string_lossy().into_owned())
    }

    /// Ignores any value associated with the current option.
    ///
    /// Call this when you want to acknowledge but discard a value
    /// without causing an error.
    pub fn ignore_value(&mut self) {
        let _ = self.raw_value();
    }

    /// Returns the program name (first argument).
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the inner iterator.
    pub fn into_inner(self) -> I {
        self.iter
    }
}

/// Parsing error types with descriptive messages
#[derive(Debug)]
pub enum ParsingError {
    /// Invalid option syntax or format
    InvalidOption {
        reason: &'static str,
        offender: Option<OsString>,
    },

    /// A value was provided but not consumed by calling `value()` or `ignore_value()`
    UnconsumedValue { value: OsString },

    /// The arguments iterator was empty (no program name)
    Empty,

    /// A string containing invalid UTF-8 was encountered
    InvalidString,

    /// An unexpected or unrecognized argument was provided
    UnexpectedArg {
        offender: String,
        value: Option<String>,
        format: &'static str,
        prefix: &'static str,
    },
}

impl Display for ParsingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidOption { reason, offender } => {
                let reserve = write!(f, "reason: {reason}");
                if let Some(sentence) = offender {
                    return write!(f, " at: {}", sentence.display());
                }

                reserve
            }

            Self::UnconsumedValue { value } => {
                write!(f, "leftover value: {}", value.display())
            }

            Self::UnexpectedArg {
                offender,
                value,
                format,
                prefix,
            } => match value {
                Some(val) => {
                    write!(f, "unexpected argument: {prefix}{offender}{format}{val}")
                }

                None => {
                    write!(f, "unexpected argument: {prefix}{offender}")
                }
            },

            Self::Empty => write!(f, "env variables were empty"),

            Self::InvalidString => write!(f, "attempt to parse invalid utf-8"),
        }
    }
}

impl Error for ParsingError {}

// Splits a long option like
// `--option=value`
// into (b"option", Some(b"value"))
//
// if it can't determine the position of the `=` character
// then the 2nd field of the tuple is `None`
fn split_long_opt_value(src: &[u8]) -> (&[u8], Option<&[u8]>) {
    let equals_pos = src.iter().position(|x| *x == b'=');

    match equals_pos {
        None => (src, None),

        Some(pos) => {
            let left = src.get(0..pos).expect("infallible");
            let right = src.get(pos + 1..);

            (left, right)
        }
    }
}

#[cfg(test)]
mod tests {
    macro_rules! test_cmdline {
        ($arr: expr) => {
            $arr.into_iter().map(|x| OsString::from(x))
        };
    }

    use crate::{Argument::*, Parser};
    use std::ffi::OsString;

    #[test]
    fn basic() {
        let content = test_cmdline!(["testbin", "-meow", "--awrff=puppy", "value"]);

        let mut parser = Parser::from_arbitrary(content).unwrap();

        assert_eq!(parser.name(), "testbin");
        assert_eq!(parser.forward().unwrap().unwrap(), Short('m'));
        assert_eq!(parser.forward().unwrap().unwrap(), Short('e'));
        assert_eq!(parser.forward().unwrap().unwrap(), Short('o'));
        assert_eq!(parser.forward().unwrap().unwrap(), Short('w'));

        assert_eq!(parser.forward().unwrap().unwrap(), Long("awrff"));
        assert!(parser.value().unwrap() == "puppy");
        assert_eq!(parser.forward().unwrap().unwrap(), Value("value"));
    }

    #[test]
    fn simple_error() {
        let content = test_cmdline!(["bin", "-this=wrong"]);

        let mut parser = Parser::from_arbitrary(content).unwrap();

        assert_eq!(parser.forward().unwrap().unwrap(), Short('t'));
        assert_eq!(parser.forward().unwrap().unwrap(), Short('h'));
        assert_eq!(parser.forward().unwrap().unwrap(), Short('i'));
        assert_eq!(parser.forward().unwrap().unwrap(), Short('s'));

        assert!(parser.forward().is_err());
    }

    #[test]
    fn argument_to_error() {
        let arg = Long("example");

        assert_eq!(
            arg.into_error("examplevalue").to_string(),
            "unexpected argument: --example=examplevalue"
        );
    }

    #[test]
    fn trailing_values() {
        let content = test_cmdline!(["testbin", "-meow", "--awrff=puppy", "--", "meow"]);

        let mut parser = Parser::from_arbitrary(content).unwrap();

        while let Some(p) = parser.forward().unwrap() {
            dbg!(p);
        }
    }
}
