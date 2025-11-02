#![warn(clippy::pedantic)]
#![warn(clippy::complexity)]
#![cfg_attr(not(feature = "std"), no_std)]
//! # Sap - a Small Argument Parser
//!
//! A minimal, zero-dependency Unix command-line argument parser for Rust.
//!
//! Sap provides full control over argument parsing with an iterator-based API that handles
//! GNU-style options while maintaining simplicity and flexibility.
//!
//! ## Features
//!
//! - **GNU-style option parsing**: Support for short (`-a`), long (`--verbose`), and combined options (`-abc`)
//! - **Flexible value handling**: Options with values via `--name=value` or separate arguments
//! - **POSIX compliance**: Handle `--` separator and `-` (stdin) arguments correctly
//! - **Zero dependencies**: Pure Rust implementation with no external crates
//! - **Iterator-based**: Works with any `Iterator<Item = Into<String>>` for maximum flexibility
//! - **Comprehensive error handling**: Descriptive error messages for invalid input
//!
//! ## Example
//!
//! ```rust
//! use sap::{Parser, Argument};
//!
//! // Parse from string arrays directly - no need to convert to String first!
//! let mut parser = Parser::from_arbitrary(["myprogram", "-v", "--file=input.txt"]).unwrap();
//!
//! while let Some(arg) = parser.forward().unwrap() {
//!     match arg {
//!         Argument::Short('v') => println!("Verbose mode enabled"),
//!         Argument::Long("file") => {
//!             if let Some(filename) = parser.value() {
//!                 println!("Processing file: {}", filename);
//!             }
//!         }
//!         Argument::Value(val) => println!("Positional argument: {}", val),
//!         _ => {}
//!     }
//! }
//! ```

#[cfg(not(feature = "std"))]
extern crate alloc;

use core::{error::Error, fmt::Display, hint::unreachable_unchecked, mem};

#[cfg(feature = "std")]
use std::{borrow::Cow, env, fmt::Debug};

#[cfg(not(feature = "std"))]
use alloc::{
    borrow::{Cow, ToOwned},
    string::{String, ToString},
};

/// A [`Result`] type alias using [`ParsingError`] as the default error type.
///
/// This type alias is used throughout the Sap API to reduce boilerplate when
/// returning parsing results.
///
/// # Examples
///
/// ```rust
/// use sap::{Result, ParsingError};
///
/// fn parse_config() -> Result<String> {
///     // Returns Result<String, ParsingError>
///     Ok("config".to_string())
/// }
/// ```
pub type Result<T, E = ParsingError> = core::result::Result<T, E>;

/// Represents a parsed command-line argument.
///
/// Each argument parsed by [`Parser::forward`] is represented as one of these variants.
/// The parser automatically categorizes arguments based on their prefix and structure.
///
/// # Examples
///
/// ```rust
/// use sap::{Parser, Argument};
///
/// let mut parser = Parser::from_arbitrary(["prog", "--verbose", "-x", "file.txt"]).unwrap();
///
/// assert_eq!(parser.forward().unwrap(), Some(Argument::Long("verbose")));
/// assert_eq!(parser.forward().unwrap(), Some(Argument::Short('x')));
/// assert_eq!(parser.forward().unwrap(), Some(Argument::Value("file.txt".into())));
/// ```
#[derive(Debug, PartialEq, PartialOrd, Ord, Eq, Hash, Clone)]
pub enum Argument<'a> {
    /// A long option starting with `--` (e.g., `--verbose`, `--file`).
    ///
    /// Long options can have associated values via `--option=value` syntax.
    /// Use [`Parser::value`] after parsing to retrieve the value if present.
    Long(&'a str),

    /// A short option starting with `-` followed by a single character (e.g., `-v`, `-x`).
    ///
    /// Short options can be combined (`-abc` becomes three separate `Short` arguments).
    /// They cannot have values attached with `=` syntax, but can consume the next argument as a value.
    Short(char),

    /// A positional argument or operand (e.g., `file.txt`, `/path/to/file`).
    ///
    /// This includes any argument that doesn't start with `-` or `--`, as well as
    /// all arguments following the `--` terminator.
    Value(Cow<'a, str>),

    /// The special `-` argument, typically representing stdin/stdout.
    ///
    /// This is commonly used in Unix tools to indicate reading from standard input
    /// or writing to standard output.
    Stdio,
}

impl<'a> Argument<'a> {
    /// Converts this argument into a [`ParsingError::UnexpectedArg`] error.
    ///
    /// This is a convenience method for creating contextual error messages when an argument
    /// is encountered but not expected by the application. The resulting error message
    /// includes appropriate formatting based on the argument type.
    ///
    /// # Parameters
    ///
    /// * `value` - Optional value associated with the argument (primarily used with options)
    ///
    /// # Examples
    ///
    /// ```rust
    /// use sap::Argument;
    ///
    /// // Long option with value
    /// let arg = Argument::Long("unknown");
    /// let error = arg.into_error(Some("value"));
    /// assert_eq!(error.to_string(), "unexpected argument: --unknown=value");
    ///
    /// // Short option without value
    /// let arg = Argument::Short('x');
    /// let error = arg.into_error(None::<&str>);
    /// assert_eq!(error.to_string(), "unexpected argument: -x");
    ///
    /// // Stdio argument
    /// let arg = Argument::Stdio;
    /// let error = arg.into_error(None::<&str>);
    /// assert_eq!(error.to_string(), "unexpected argument: -");
    /// ```
    pub fn into_error<A>(self, value: A) -> ParsingError
    where
        A: Into<Option<&'a str>>,
    {
        use Argument::{Long, Short, Stdio, Value};

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
            Stdio => ParsingError::UnexpectedArg {
                offender: "-".to_string(),
                value: None,
                format: "",
                prefix: "",
            },
        }
    }
}

impl Display for Argument<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Argument::{Long, Short, Stdio, Value};

        match self {
            Long(s) => write!(f, "--{s}"),
            Short(ch) => write!(f, "-{ch}"),
            Value(cow) => write!(f, "{cow}"),
            Stdio => write!(f, "-"),
        }
    }
}

/// A stateful command-line argument parser.
///
/// The `Parser` processes arguments one at a time using an iterator-based approach,
/// maintaining internal state to handle complex scenarios like combined short options
/// and option values.
///
/// # Type Parameters
///
/// * `I` - An iterator that yields items convertible to `String` (e.g., `&str`, `String`, `OsString`)
///
/// # Examples
///
/// ```rust
/// use sap::{Parser, Argument};
///
/// // Parse from environment arguments
/// let mut parser = Parser::from_env().unwrap();
///
/// // Or parse from string arrays directly
/// let mut parser = Parser::from_arbitrary(["myprogram", "-abc", "--verbose"]).unwrap();
///
/// // Process arguments one by one
/// while let Some(arg) = parser.forward().unwrap() {
///     match arg {
///         Argument::Short(c) => println!("Short option: -{}", c),
///         Argument::Long(name) => println!("Long option: --{}", name),
///         Argument::Value(val) => println!("Value: {}", val),
///         Argument::Stdio => println!("Stdin/stdout argument"),
///     }
/// }
/// ```
pub struct Parser<I: Iterator> {
    iter: I,
    state: State,
    name: String,
    last_arg: String,
}

/// Internal parser state for handling complex parsing scenarios.
///
/// The parser uses this state machine to track context between calls to [`Parser::forward`],
/// enabling proper handling of combined options, option values, and argument terminators.
enum State {
    /// Normal parsing state with no special context.
    NotInteresting,
    /// Contains a value from a previous option (e.g., from `--option=value`).
    LeftoverValue(String),
    /// Processing combined short options like `-abc` (position in string, remaining chars).
    Combined(usize, String),
    /// All remaining arguments are positional values (after encountering `--`).
    End,
    /// Parser encountered an error and stopped consuming from the underlying iterator.
    Poisoned,
}

#[cfg(feature = "std")]
impl Parser<env::Args> {
    /// Creates a `Parser` using the program's command-line arguments from [`std::env::args`].
    ///
    /// This is the most common way to create a parser for typical CLI applications.
    /// The first argument (program name) is consumed and can be accessed via [`Parser::name`].
    ///
    /// # Errors
    ///
    /// Returns [`ParsingError::Empty`] if no arguments are available (which should not
    /// happen in normal program execution).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use sap::Parser;
    ///
    /// let parser = Parser::from_env().unwrap();
    /// println!("Program name: {}", parser.name());
    /// ```
    pub fn from_env() -> Result<Self> {
        Self::from_arbitrary(env::args())
    }
}

impl<I, V> Parser<I>
where
    I: Iterator<Item = V>,
    V: Into<String>,
{
    /// Creates a `Parser` from any iterator that yields items convertible to `String`.
    ///
    /// This method provides maximum flexibility for parsing argument lists. You can pass
    /// string arrays, vectors, or any other iterable collection of string-like items.
    /// This is particularly useful for testing and when arguments come from sources
    /// other than the command line.
    ///
    /// The first item from the iterator is treated as the program name and can be
    /// accessed via [`Parser::name`]. All subsequent items are parsed as arguments.
    ///
    /// # Errors
    ///
    /// Returns [`ParsingError::Empty`] if the iterator is empty.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use sap::Parser;
    ///
    /// // Parse from string arrays directly
    /// let parser = Parser::from_arbitrary(["myprogram", "-v", "file.txt"]).unwrap();
    /// assert_eq!(parser.name(), "myprogram");
    ///
    /// // Also works with vectors of strings
    /// let args = vec!["prog".to_string(), "--verbose".to_string()];
    /// let parser = Parser::from_arbitrary(args).unwrap();
    /// ```
    pub fn from_arbitrary<A>(iter: A) -> Result<Parser<I>>
    where
        A: IntoIterator<IntoIter = I>,
    {
        let mut iter = iter.into_iter();
        let name = iter.next().ok_or(ParsingError::Empty)?.into();

        Ok(Parser {
            iter,
            state: State::NotInteresting,
            name,
            last_arg: String::new(),
        })
    }

    /// Advances the parser to the next argument and returns it.
    ///
    /// This is the main parsing method. Call it repeatedly to process all arguments.
    /// The parser maintains state between calls to properly handle complex scenarios
    /// like combined short options (`-abc`) and option values.
    ///
    /// # Returns
    ///
    /// - `Some(arg)` - Successfully parsed the next argument
    /// - `None` - No more arguments to process
    ///
    /// # Errors
    ///
    /// Returns an error when:
    /// - Short options have attached values using `=` (e.g., `-x=value`)
    /// - Option values are left unconsumed from previous calls
    /// - Invalid argument syntax is encountered
    ///
    /// ## Poisoned State
    ///
    /// After returning an error, the parser enters a "poisoned" state where:
    /// - All subsequent calls to `forward()` will return `Ok(None)`
    /// - The underlying iterator will not be polled further
    /// - The iterator can still be recovered using [`Parser::into_inner`] if needed
    ///
    /// This ensures predictable behavior after errors and allows recovering the
    /// remaining unparsed arguments without risking inconsistent parser state.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use sap::{Parser, Argument};
    ///
    /// let mut parser = Parser::from_arbitrary(["prog", "-abc", "--file=test.txt"]).unwrap();
    ///
    /// // Combined short options are parsed individually
    /// assert_eq!(parser.forward().unwrap(), Some(Argument::Short('a')));
    /// assert_eq!(parser.forward().unwrap(), Some(Argument::Short('b')));
    /// assert_eq!(parser.forward().unwrap(), Some(Argument::Short('c')));
    ///
    /// // Long option with attached value
    /// assert_eq!(parser.forward().unwrap(), Some(Argument::Long("file")));
    /// assert_eq!(parser.value(), Some("test.txt".to_string()));
    ///
    /// assert_eq!(parser.forward().unwrap(), None);
    /// ```
    pub fn forward(&mut self) -> Result<Option<Argument<'_>>> {
        loop {
            match self.state {
                State::Poisoned => return Ok(None),
                State::End => {
                    return Ok(self
                        .iter
                        .next()
                        .map(|v| Argument::Value(Cow::Owned(v.into()))));
                }
                State::Combined(index, ref mut options) => {
                    let options = mem::take(options);

                    match options.chars().nth(index) {
                        Some(char) => {
                            if char == '=' {
                                self.state = State::Poisoned;

                                return Err(ParsingError::InvalidOption {
                                    reason: "Short options do not support values",
                                    offender: None,
                                });
                            }

                            self.state = State::Combined(index + 1, options);

                            return Ok(Some(Argument::Short(char)));
                        }
                        None => self.state = State::NotInteresting,
                    }
                }
                State::NotInteresting => {
                    self.last_arg = match self.iter.next() {
                        Some(s) => s.into(),
                        None => return Ok(None),
                    };

                    match self.last_arg.strip_prefix("-") {
                        Some("") => return Ok(Some(Argument::Stdio)),
                        Some("-") => {
                            self.state = State::End;
                        }
                        Some(rest) => {
                            if rest.starts_with('-') {
                                if let Some(index) = self.last_arg.find('=') {
                                    self.state =
                                        State::LeftoverValue(self.last_arg[index + 1..].to_owned());

                                    return Ok(Some(Argument::Long(&self.last_arg[2..index])));
                                }

                                return Ok(Some(Argument::Long(&self.last_arg[2..])));
                            }

                            self.state = State::Combined(0, rest.to_owned());
                        }

                        None => {
                            return Ok(Some(Argument::Value(Cow::Borrowed(&self.last_arg))));
                        }
                    }
                }
                State::LeftoverValue(ref mut value) => {
                    let value = mem::take(value);
                    mem::swap(&mut self.state, &mut State::Poisoned);

                    return Err(ParsingError::UnconsumedValue { value });
                }
            };
        }
    }

    /// Retrieves and consumes the value associated with the most recent option.
    ///
    /// Call this method after parsing a long option that may have an attached value
    /// (using `--option=value` syntax). The value is consumed and subsequent calls
    /// will return `None` until another option with a value is parsed.
    ///
    /// # Returns
    ///
    /// - `Some(value)` - The option has an attached value
    /// - `None` - The option has no attached value or it was already consumed
    ///
    /// # Examples
    ///
    /// ```rust
    /// use sap::{Parser, Argument};
    ///
    /// let mut parser = Parser::from_arbitrary(["prog", "--file=input.txt", "--verbose"]).unwrap();
    ///
    /// // Option with attached value
    /// assert_eq!(parser.forward().unwrap(), Some(Argument::Long("file")));
    /// assert_eq!(parser.value(), Some("input.txt".to_string()));
    /// assert_eq!(parser.value(), None); // Already consumed
    ///
    /// // Option without value
    /// assert_eq!(parser.forward().unwrap(), Some(Argument::Long("verbose")));
    /// assert_eq!(parser.value(), None);
    /// ```
    pub fn value(&mut self) -> Option<String> {
        match self.state {
            State::LeftoverValue(_) => match mem::replace(&mut self.state, State::NotInteresting) {
                State::LeftoverValue(val) => Some(val),
                _ => unsafe { unreachable_unchecked() },
            },
            _ => None,
        }
    }

    /// Discards any value associated with the most recent option.
    ///
    /// This is a convenience method that calls [`Parser::value`] and discards the result.
    /// Use this when you know an option might have a value but you don't need it,
    /// preventing unconsumed value errors.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use sap::{Parser, Argument};
    ///
    /// let mut parser = Parser::from_arbitrary(["prog", "--debug=verbose"]).unwrap();
    ///
    /// assert_eq!(parser.forward().unwrap(), Some(Argument::Long("debug")));
    /// parser.ignore_value(); // Discard the "verbose" value
    /// ```
    pub fn ignore_value(&mut self) {
        let _ = self.value();
    }

    /// Returns the program name (the first argument from the iterator).
    ///
    /// This is typically the name or path of the executable, depending on how
    /// the program was invoked.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use sap::Parser;
    ///
    /// let parser = Parser::from_arbitrary(["/usr/bin/myprogram", "-v"]).unwrap();
    /// assert_eq!(parser.name(), "/usr/bin/myprogram");
    /// ```
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns `true` if the parser is in a poisoned state due to a previous error.
    ///
    /// When poisoned, `forward()` will always return `Ok(None)`. Use `into_inner()`
    /// to recover the underlying iterator if needed.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use sap::{Parser, Argument};
    ///
    /// let mut parser = Parser::from_arbitrary(["prog", "--file=test"]).unwrap();
    ///
    /// assert!(!parser.is_poisoned());
    ///
    /// // Parse option without consuming value
    /// parser.forward().unwrap();
    ///
    /// // This errors and poisons the parser
    /// assert!(parser.forward().is_err());
    /// assert!(parser.is_poisoned());
    /// ```
    pub const fn is_poisoned(&self) -> bool {
        matches!(self.state, State::Poisoned)
    }

    /// Returns `true` if there is an unconsumed value from a previous option.
    ///
    /// This occurs when parsing options like `--file=value` where the value has not
    /// yet been retrieved via `value()` or discarded via `ignore_value()`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use sap::{Parser, Argument};
    ///
    /// let mut parser = Parser::from_arbitrary(["prog", "--file=test.txt"]).unwrap();
    ///
    /// assert!(!parser.has_leftover_value());
    ///
    /// // Parse the option
    /// parser.forward().unwrap();
    ///
    /// // Now there's a leftover value
    /// assert!(parser.has_leftover_value());
    ///
    /// // Consume it
    /// parser.value();
    /// assert!(!parser.has_leftover_value());
    /// ```
    pub const fn has_leftover_value(&self) -> bool {
        matches!(self.state, State::LeftoverValue(_))
    }

    /// Consumes the parser and returns the underlying iterator.
    ///
    /// This allows access to any remaining, unparsed arguments. Note that the
    /// iterator's state reflects the current parsing position.
    ///
    /// # Error Recovery
    ///
    /// This method is particularly useful for recovering unparsed arguments after
    /// a parsing error occurs. When the parser enters a poisoned state due to an error,
    /// the underlying iterator remains intact and can be retrieved to access the
    /// remaining arguments that were not yet consumed.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use sap::{Parser, Argument};
    ///
    /// let mut parser = Parser::from_arbitrary(["prog", "-v", "remaining"]).unwrap();
    ///
    /// // Parse one argument
    /// parser.forward().unwrap();
    ///
    /// // Get the remaining iterator
    /// let remaining: Vec<String> = parser.into_inner().map(|s| s.into()).collect();
    /// assert_eq!(remaining, vec!["remaining"]);
    /// ```
    ///
    /// ```rust
    /// use sap::{Parser, Argument};
    ///
    /// let mut parser = Parser::from_arbitrary(["prog", "--file=test", "--other"]).unwrap();
    ///
    /// // Parse first option but forget to consume value
    /// assert_eq!(parser.forward().unwrap(), Some(Argument::Long("file")));
    ///
    /// // This will error due to unconsumed value, poisoning the parser
    /// assert!(parser.forward().is_err());
    ///
    /// // Recover the remaining unparsed arguments
    /// let remaining: Vec<String> = parser.into_inner().map(|s| s.into()).collect();
    /// assert_eq!(remaining, vec!["--other"]);
    /// ```
    pub fn into_inner(self) -> I {
        self.iter
    }
}

/// Errors that can occur during argument parsing.
///
/// All parsing operations return a `Result` with this error type. Each variant
/// provides specific context about what went wrong during parsing.
#[derive(Debug)]
pub enum ParsingError {
    /// Invalid option syntax or format was encountered.
    ///
    /// This typically occurs when:
    /// - Short options are given values with `=` syntax (e.g., `-x=value`)
    /// - Malformed option syntax is detected
    ///
    /// # Fields
    ///
    /// * `reason` - Human-readable description of what was invalid
    /// * `offender` - The specific argument that caused the error (if available)
    InvalidOption {
        reason: &'static str,
        offender: Option<String>,
    },

    /// An option value was not consumed after being parsed.
    ///
    /// This occurs when a long option has an attached value (e.g., `--file=input.txt`)
    /// but the application doesn't call [`Parser::value`] or [`Parser::ignore_value`]
    /// before parsing the next argument.
    ///
    /// # Fields
    ///
    /// * `value` - The unconsumed value that was attached to the option
    UnconsumedValue { value: String },

    /// The argument iterator was empty (contained no program name).
    ///
    /// This should not occur during normal program execution but may happen
    /// when creating parsers from empty custom iterators.
    Empty,

    /// An unexpected or unrecognized argument was encountered.
    ///
    /// This error is typically created by calling [`Argument::into_error`] when
    /// the application encounters an argument it doesn't know how to handle.
    ///
    /// # Fields
    ///
    /// * `offender` - The argument name that was unexpected
    /// * `value` - Associated value (if any)
    /// * `format` - How the value is formatted in error messages (e.g., "=" or " ")
    /// * `prefix` - The argument prefix (e.g., "--" for long options, "-" for short)
    UnexpectedArg {
        offender: String,
        value: Option<String>,
        format: &'static str,
        prefix: &'static str,
    },
}

impl Display for ParsingError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::InvalidOption { reason, offender } => {
                write!(f, "reason: {reason}")?;
                if let Some(sentence) = offender {
                    write!(f, " at: {sentence}")?;
                }

                Ok(())
            }

            Self::UnconsumedValue { value } => {
                write!(f, "leftover value: {value}",)
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
        }
    }
}

impl Error for ParsingError {}

#[cfg(feature = "std")]
#[cfg(test)]
mod tests {
    use crate::{Argument::*, Parser, Result};

    #[test]
    fn parser_creation() -> Result<()> {
        let parser = Parser::from_env()?;
        assert!(!parser.name().is_empty());

        let parser = Parser::from_arbitrary(["test"])?;
        assert_eq!(parser.name(), "test");

        let parser = Parser::from_arbitrary(["/usr/bin/program", "-v"])?;
        assert_eq!(parser.name(), "/usr/bin/program");

        assert!(Parser::from_arbitrary::<[&str; 0]>([]).is_err());
        Ok(())
    }

    #[test]
    fn short_options() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "-a", "-b", "-c"])?;
        assert_eq!(parser.forward()?, Some(Short('a')));
        assert_eq!(parser.forward()?, Some(Short('b')));
        assert_eq!(parser.forward()?, Some(Short('c')));
        assert_eq!(parser.forward()?, None);
        Ok(())
    }

    #[test]
    fn short_option_clustering() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "-abc"])?;
        assert_eq!(parser.forward()?, Some(Short('a')));
        assert_eq!(parser.forward()?, Some(Short('b')));
        assert_eq!(parser.forward()?, Some(Short('c')));
        assert_eq!(parser.forward()?, None);
        Ok(())
    }

    #[test]
    fn short_option_special_chars() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "-1", "-@", "-ñ"])?;
        assert_eq!(parser.forward()?, Some(Short('1')));
        assert_eq!(parser.forward()?, Some(Short('@')));
        assert_eq!(parser.forward()?, Some(Short('ñ')));
        assert_eq!(parser.forward()?, None);
        Ok(())
    }

    #[test]
    fn short_option_equals_error() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "-x=value"])?;
        assert_eq!(parser.forward()?, Some(Short('x')));
        assert!(parser.forward().is_err());
        Ok(())
    }

    #[test]
    fn long_options() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "--verbose", "--help"])?;
        assert_eq!(parser.forward()?, Some(Long("verbose")));
        assert_eq!(parser.value(), None);
        assert_eq!(parser.forward()?, Some(Long("help")));
        assert_eq!(parser.forward()?, None);
        Ok(())
    }

    #[test]
    fn long_option_with_value() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "--file=test.txt"])?;
        assert_eq!(parser.forward()?, Some(Long("file")));
        assert_eq!(parser.value(), Some("test.txt".to_string()));
        assert_eq!(parser.value(), None);
        assert_eq!(parser.forward()?, None);
        Ok(())
    }

    #[test]
    fn long_option_empty_value() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "--empty="])?;
        assert_eq!(parser.forward()?, Some(Long("empty")));
        assert_eq!(parser.value(), Some(String::new()));
        assert_eq!(parser.forward()?, None);
        Ok(())
    }

    #[test]
    fn long_option_complex_values() -> Result<()> {
        let mut parser =
            Parser::from_arbitrary(["prog", "--equation=x=y+z", "--spaces=hello world"])?;

        assert_eq!(parser.forward()?, Some(Long("equation")));
        assert_eq!(parser.value(), Some("x=y+z".to_string()));

        assert_eq!(parser.forward()?, Some(Long("spaces")));
        assert_eq!(parser.value(), Some("hello world".to_string()));

        assert_eq!(parser.forward()?, None);
        Ok(())
    }

    #[test]
    fn positional_args() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "file1", "file2", "file3"])?;
        assert_eq!(parser.forward()?, Some(Value("file1".into())));
        assert_eq!(parser.forward()?, Some(Value("file2".into())));
        assert_eq!(parser.forward()?, Some(Value("file3".into())));
        assert_eq!(parser.forward()?, None);
        Ok(())
    }

    #[test]
    fn stdio_argument() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "-"])?;
        assert_eq!(parser.forward()?, Some(Stdio));
        assert_eq!(parser.forward()?, None);

        let mut parser = Parser::from_arbitrary(["prog", "-v", "-", "--help"])?;
        assert_eq!(parser.forward()?, Some(Short('v')));
        assert_eq!(parser.forward()?, Some(Stdio));
        assert_eq!(parser.forward()?, Some(Long("help")));
        assert_eq!(parser.forward()?, None);
        Ok(())
    }

    #[test]
    fn double_dash_terminator() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "-v", "--", "--not-an-option", "-x"])?;
        assert_eq!(parser.forward()?, Some(Short('v')));
        assert_eq!(parser.forward()?, Some(Value("--not-an-option".into())));
        assert_eq!(parser.forward()?, Some(Value("-x".into())));
        assert_eq!(parser.forward()?, None);

        let mut parser = Parser::from_arbitrary(["prog", "--"])?;
        assert_eq!(parser.forward()?, None);

        let mut parser = Parser::from_arbitrary(["prog", "--", "file1", "file2"])?;
        assert_eq!(parser.forward()?, Some(Value("file1".into())));
        assert_eq!(parser.forward()?, Some(Value("file2".into())));
        assert_eq!(parser.forward()?, None);
        Ok(())
    }

    #[test]
    fn stdio_after_double_dash() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "-", "--", "-", "file"])?;
        assert_eq!(parser.forward()?, Some(Stdio));
        assert_eq!(parser.forward()?, Some(Value("-".into())));
        assert_eq!(parser.forward()?, Some(Value("file".into())));
        assert_eq!(parser.forward()?, None);
        Ok(())
    }

    #[test]
    fn mixed_arguments() -> Result<()> {
        let mut parser = Parser::from_arbitrary([
            "prog",
            "-abc",
            "--verbose",
            "-f",
            "file.txt",
            "--output=result.txt",
            "--",
            "pos1",
            "-x",
        ])?;

        assert_eq!(parser.forward()?, Some(Short('a')));
        assert_eq!(parser.forward()?, Some(Short('b')));
        assert_eq!(parser.forward()?, Some(Short('c')));
        assert_eq!(parser.forward()?, Some(Long("verbose")));
        assert_eq!(parser.forward()?, Some(Short('f')));
        assert_eq!(parser.forward()?, Some(Value("file.txt".into())));
        assert_eq!(parser.forward()?, Some(Long("output")));
        assert_eq!(parser.value(), Some("result.txt".to_string()));
        assert_eq!(parser.forward()?, Some(Value("pos1".into())));
        assert_eq!(parser.forward()?, Some(Value("-x".into())));
        assert_eq!(parser.forward()?, None);
        Ok(())
    }

    #[test]
    fn value_consumption() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "--file=test.txt", "--verbose"])?;

        assert_eq!(parser.forward()?, Some(Long("file")));
        assert_eq!(parser.value(), Some("test.txt".to_string()));
        assert_eq!(parser.value(), None);

        assert_eq!(parser.forward()?, Some(Long("verbose")));
        parser.ignore_value();

        assert_eq!(parser.forward()?, None);
        Ok(())
    }

    #[test]
    fn unicode_support() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "--файл=документ.txt", "-ñ"])?;
        assert_eq!(parser.forward()?, Some(Long("файл")));
        assert_eq!(parser.value(), Some("документ.txt".to_string()));
        assert_eq!(parser.forward()?, Some(Short('ñ')));
        assert_eq!(parser.forward()?, None);
        Ok(())
    }

    #[test]
    fn empty_and_whitespace() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "", "--msg=hello world"])?;
        assert_eq!(parser.forward()?, Some(Value("".into())));
        assert_eq!(parser.forward()?, Some(Long("msg")));
        assert_eq!(parser.value(), Some("hello world".to_string()));
        assert_eq!(parser.forward()?, None);
        Ok(())
    }

    #[test]
    fn unconsumed_value_error() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "--file=test.txt", "--verbose"])?;
        assert_eq!(parser.forward()?, Some(Long("file")));
        assert!(parser.forward().is_err());
        Ok(())
    }

    #[test]
    fn into_inner() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "-v", "remaining1", "remaining2"])?;
        assert_eq!(parser.forward()?, Some(Short('v')));

        let remaining: Vec<_> = parser.into_inner().collect();
        assert_eq!(remaining, ["remaining1", "remaining2"]);
        Ok(())
    }

    #[test]
    fn argument_into_error() {
        assert_eq!(
            Long("test").into_error("value").to_string(),
            "unexpected argument: --test=value"
        );
        assert_eq!(
            Long("test").into_error(None::<&str>).to_string(),
            "unexpected argument: --test"
        );
        assert_eq!(
            Short('x').into_error("val").to_string(),
            "unexpected argument: -x val"
        );
        assert_eq!(
            Short('x').into_error(None::<&str>).to_string(),
            "unexpected argument: -x"
        );
        assert_eq!(
            Value("file".into()).into_error(None::<&str>).to_string(),
            "unexpected argument: file"
        );
        assert_eq!(
            Stdio.into_error(None::<&str>).to_string(),
            "unexpected argument: -"
        );
    }

    #[test]
    fn gnu_style_parsing() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "-a", "operand", "-b"])?;
        assert_eq!(parser.forward()?, Some(Short('a')));
        assert_eq!(parser.forward()?, Some(Value("operand".into())));
        assert_eq!(parser.forward()?, Some(Short('b')));
        assert_eq!(parser.forward()?, None);
        Ok(())
    }

    #[test]
    fn stress_test() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog"])?;
        assert_eq!(parser.forward()?, None);

        let long_name = "a".repeat(1000);
        let long_option = format!("--{long_name}");
        let mut parser = Parser::from_arbitrary(["prog", &long_option])?;
        if let Some(Long(name)) = parser.forward()? {
            assert_eq!(name, long_name);
        }
        Ok(())
    }
}
