#![warn(clippy::pedantic)]
#![warn(clippy::complexity)]
//! Sap - a Small Argument Parser
//!
//! The only upside (currently) is being very minimal.
//!
//! Unix only.

use std::{
    env,
    error::Error,
    ffi::OsString,
    fmt::{Debug, Display},
    mem,
    os::unix::ffi::{OsStrExt, OsStringExt},
};

pub type Result<T, E = ParsingError> = core::result::Result<T, E>;

/// Represents a command-line argument
#[derive(Debug, PartialEq, PartialOrd, Ord, Eq, Hash, Clone, Copy)]
pub enum Argument<'a> {
    /// Represents an long option like
    /// `--example`.
    Long(&'a str),

    /// Represets a singular character
    /// option, as in: `-q`
    Short(char),

    /// Regular argument
    /// like `/proc/meminfo`
    Lonely(&'a str),
}

impl<'a> Argument<'a> {
    pub fn into_error<A>(self, value: A) -> ParsingError
    where
        A: Into<Option<&'a str>>,
    {
        use Argument::{Lonely, Long, Short};

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

                // cheap trick
                // omit it one day.
                format: " ",

                prefix: "-",
            },

            Lonely(arg) => ParsingError::UnexpectedArg {
                offender: arg.to_string(),
                value: None,
                format: "",

                prefix: "",
            },
        }
    }
}

enum State {
    NotInteresting,
    LeftoverValue(OsString),
    Combined(usize, OsString),
    End,
}

/// Parser of the command-line arguments
/// internally uses the `ArgsOs` iterator
/// when created via the `parser_from_env`
/// function.
pub struct Parser<I> {
    iter: I,
    state: State,

    // TODO: use these two for better errors.
    last_short: Option<char>,
    last_long: Option<OsString>,

    name: String,
}

impl<I> Parser<I>
where
    I: Iterator<Item = OsString>,
{
    /// Moves the parser one option forward
    /// if it hits a `--`, it will start returning `None`
    ///
    /// This happens because `--` signifies the end of arguments.
    pub fn forward(&mut self) -> Option<Result<Argument<'_>>> {
        if matches!(self.state, State::End) {
            return None;
        }

        match self.state {
            State::End => return None,
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

                    return Some(Err(err));
                }

                Some(ch) => {
                    *pos += 1;

                    return Some(Ok(Argument::Short(*ch as char)));
                }
            },

            _ => {}
        }

        let arg = match self.iter.next() {
            None => return None,
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
            return None;
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

                        return Some(Err(err));
                    }
                    Ok(val) => val,
                };
                Some(Ok(Argument::Long(str_arg)))

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
                    Some(Ok(Argument::Short(char)))
                } else {
                    // lonely `-`
                    // probably an error on the user's part
                    // but syntatically correct.
                    Some(Ok(Argument::Lonely("-")))
                }
            }
        } else {
            // might not be needed,
            // however i am not sure of the user's
            // eternal glory and shine
            let str_arg = match str::from_utf8(arg.as_encoded_bytes()) {
                Err(_e) => {
                    let err = ParsingError::InvalidString;

                    return Some(Err(err));
                }
                Ok(val) => val,
            };

            // lonely value
            Some(Ok(Argument::Lonely(str_arg)))
        }
    }

    /// Retrieves the value stored in the Parser
    /// without converting it to a UTF-8 string.
    /// not retrieving this value becomes an error.
    pub fn val_raw(&mut self) -> Option<OsString> {
        match self.state {
            State::LeftoverValue(_) => match mem::replace(&mut self.state, State::NotInteresting) {
                State::LeftoverValue(val) => Some(val),
                _ => unreachable!(),
            },

            _ => None,
        }
    }

    /// Retrieves the value
    /// returns `Some` if the data could be converted
    /// to valid Unicode else returns `None`,
    /// however even if it returns `None`, the value is consumed.
    ///
    /// This operation currently might be expensive.
    pub fn val_utf8(&mut self) -> Option<String> {
        match self.val_raw() {
            Some(str) => str.into_string().ok(),

            None => None,
        }
    }

    /// Ignore the value
    /// to not error out the parser
    pub fn ignore_val(&mut self) {
        let _value = self.val_raw();
    }

    /// Retrieve the name of the process
    pub fn name(&self) -> &str {
        &self.name
    }
}

// TODO: Make this a nice iterator too!
#[allow(dead_code)]
struct ParserIter<I: Iterator<Item = OsString>> {
    inner: Parser<I>,
}

/// Error type describing the various ways
/// this algorithm can fail
/// and/or be induced to fail.
#[derive(Debug)]
pub enum ParsingError {
    /// Something was wrong with a provided option.
    InvalidOption {
        reason: &'static str,
        offender: Option<OsString>,
    },

    /// The value left after processing a long option
    /// was not consumed.
    UnconsumedValue { value: OsString },

    /// The initial iterator was empty.
    Empty,

    /// The string is invalid.
    InvalidString,

    /// This error is not used by the parser,
    /// however it is there to let users
    /// create errors from
    /// arguments that they deem unexpected
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
                let reserve = writeln!(f, "reason: {reason}");
                if let Some(sentence) = offender {
                    return writeln!(f, "at: {}", sentence.display());
                }

                reserve
            }

            Self::UnconsumedValue { value } => {
                writeln!(f, "leftover value: {}", value.display())
            }

            Self::UnexpectedArg {
                offender,
                value,
                format,
                prefix,
            } => match value {
                Some(val) => {
                    writeln!(f, "unexpected argument: {prefix}{offender}{format}{val}")
                }

                None => {
                    writeln!(f, "unexpected argument: {prefix}{offender}")
                }
            },

            Self::Empty => writeln!(f, "env variables were empty"),

            Self::InvalidString => writeln!(f, "attempt to parse invalid utf-8"),
        }
    }
}

impl Error for ParsingError {
    fn description(&self) -> &str {
        match self {
            Self::InvalidOption { .. } => "an invalid option was given to the command line",

            Self::UnconsumedValue { .. } => "a value was left unprocessed, after retrieval",

            Self::Empty => "env variables were empty",

            Self::InvalidString => "attempt to parse invalid utf-8",

            Self::UnexpectedArg { .. } => "an unexpected argument was passed",
        }
    }
}

/// Creates a `Parser` using the `ArgsOs` iterator
/// provided by the standard library.
///
/// # Errors
///
/// At creation it checks the created `Iterator`
/// if it contains the first value (the process name),
/// if it does not contain it and/or the value is malformed
/// the function will return `Err`
pub fn parser_from_env() -> Result<Parser<env::ArgsOs>> {
    let mut iter = env::args_os();
    let name = match iter.next() {
        None => {
            let err = ParsingError::Empty;

            return Err(err);
        }
        Some(val) => match val.into_string() {
            Ok(str) => str,
            Err(_e) => return Err(ParsingError::InvalidString),
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

/// Creates a `Parser` from an arbitrary `Iterator` with
/// `Item` as `OsString`.
///
/// # Errors
///
/// Same quirks happen as with `parser_from_env`
pub fn arbitrary_parser<I>(mut iter: I) -> Result<Parser<I>>
where
    I: Iterator<Item = OsString>,
{
    let name = match iter.next() {
        None => {
            let err = ParsingError::Empty;

            return Err(err);
        }
        Some(val) => match val.into_string() {
            Ok(str) => str,
            Err(_e) => return Err(ParsingError::InvalidString),
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

    use crate::{Argument::*, arbitrary_parser};
    use std::ffi::OsString;

    #[test]
    fn basic() {
        let content = test_cmdline!(["testbin", "-meow", "--awrff=puppy", "value"]);

        let mut parser = arbitrary_parser(content).unwrap();

        assert_eq!(parser.name(), "testbin");
        assert_eq!(parser.forward().unwrap().unwrap(), Short('m'));
        assert_eq!(parser.forward().unwrap().unwrap(), Short('e'));
        assert_eq!(parser.forward().unwrap().unwrap(), Short('o'));
        assert_eq!(parser.forward().unwrap().unwrap(), Short('w'));

        assert_eq!(parser.forward().unwrap().unwrap(), Long("awrff"));
        assert!(parser.val_utf8().unwrap() == "puppy");
        assert_eq!(parser.forward().unwrap().unwrap(), Lonely("value"));
    }

    #[test]
    fn simple_error() {
        let content = test_cmdline!(["bin", "-this=wrong"]);

        let mut parser = arbitrary_parser(content).unwrap();

        assert_eq!(parser.forward().unwrap().unwrap(), Short('t'));
        assert_eq!(parser.forward().unwrap().unwrap(), Short('h'));
        assert_eq!(parser.forward().unwrap().unwrap(), Short('i'));
        assert_eq!(parser.forward().unwrap().unwrap(), Short('s'));

        assert!(parser.forward().unwrap().is_err());
    }

    #[test]
    fn argument_to_error() {
        let arg = Long("example");

        assert_eq!(
            arg.into_error("examplevalue").to_string(),
            "unexpected argument: --example=examplevalue\n"
        );
    }
}
