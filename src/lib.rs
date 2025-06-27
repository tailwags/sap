#![warn(clippy::pedantic)]
#![warn(clippy::complexity)]
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
//! - **Iterator-based**: Works with any `Iterator<Item = String>` for maximum flexibility
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

use std::{
    borrow::Cow,
    env,
    error::Error,
    fmt::{Debug, Display},
    hint::unreachable_unchecked,
    mem,
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
    last_arg: Option<String>,
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
}

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
            last_arg: None,
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
    /// **Important**: The parser should not be used after encountering an error.
    /// The internal state becomes undefined and further parsing may produce incorrect results.
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
        if matches!(self.state, State::End) {
            return Ok(self
                .iter
                .next()
                .map(|v| Argument::Value(Cow::Owned(v.into()))));
        }

        if let State::Combined(index, ref mut options) = self.state {
            let options = mem::take(options);

            match options.chars().nth(index) {
                Some(char) => {
                    if char == '=' {
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

        let arg = match self.iter.next() {
            Some(value) => value.into(),
            None => return Ok(None),
        };

        self.last_arg = Some(arg);

        let arg = unsafe { self.last_arg.as_deref().unwrap_unchecked() };

        if arg.starts_with('-') {
            match arg.get(1..) {
                Some("-") => {
                    self.state = State::End;

                    return Ok(self
                        .iter
                        .next()
                        .map(|v| Argument::Value(Cow::Owned(v.into()))));
                }
                Some(rest) => {
                    if let Some((_, option)) = rest.split_once('-') {
                        if let Some((option, value)) = option.split_once('=') {
                            self.state = State::LeftoverValue(value.to_owned());

                            return Ok(Some(Argument::Long(option)));
                        }

                        if let State::LeftoverValue(ref mut value) = self.state {
                            return Err(ParsingError::UnconsumedValue {
                                value: mem::take(value),
                            });
                        }

                        return Ok(Some(Argument::Long(option)));
                    }

                    if let Some(option) = rest.chars().next() {
                        self.state = State::Combined(1, rest.to_owned());

                        return Ok(Some(Argument::Short(option)));
                    }

                    return Ok(Some(Argument::Stdio));
                }
                None => unsafe { unreachable_unchecked() },
            }
        }

        Ok(Some(Argument::Value(arg.into())))
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

    /// Consumes the parser and returns the underlying iterator.
    ///
    /// This allows access to any remaining, unparsed arguments. Note that the
    /// iterator's state reflects the current parsing position.
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
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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

#[cfg(test)]
mod tests {
    use crate::{Argument::*, Parser, Result};

    // Basic functionality tests
    #[test]
    fn basic() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["testbin", "-meow", "--awrff=puppy", "value"])?;

        assert_eq!(parser.name(), "testbin");
        assert_eq!(parser.forward()?, Some(Short('m')));
        assert_eq!(parser.forward()?, Some(Short('e')));
        assert_eq!(parser.forward()?, Some(Short('o')));
        assert_eq!(parser.forward()?, Some(Short('w')));

        assert_eq!(parser.forward()?, Some(Long("awrff")));
        assert_eq!(parser.value().as_deref(), Some("puppy"));
        assert_eq!(parser.forward()?, Some(Value("value".into())));

        assert!(parser.forward()?.is_none());
        Ok(())
    }

    #[test]
    fn simple_error() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["bin", "-this=wrong"])?;

        assert_eq!(parser.forward()?, Some(Short('t')));
        assert_eq!(parser.forward()?, Some(Short('h')));
        assert_eq!(parser.forward()?, Some(Short('i')));
        assert_eq!(parser.forward()?, Some(Short('s')));

        assert!(parser.forward().is_err());
        Ok(())
    }

    #[test]
    fn argument_to_error() {
        // Test Long argument with value
        let arg = Long("example");
        assert_eq!(
            arg.into_error("examplevalue").to_string(),
            "unexpected argument: --example=examplevalue"
        );

        // Test Long argument without value
        let arg = Long("verbose");
        assert_eq!(
            arg.into_error(None::<&str>).to_string(),
            "unexpected argument: --verbose"
        );

        // Test Short argument with value
        let arg = Short('f');
        assert_eq!(
            arg.into_error("file.txt").to_string(),
            "unexpected argument: -f file.txt"
        );

        // Test Short argument without value
        let arg = Short('v');
        assert_eq!(
            arg.into_error(None::<&str>).to_string(),
            "unexpected argument: -v"
        );

        // Test Value argument
        let arg = Value("filename.txt".into());
        assert_eq!(
            arg.into_error(None::<&str>).to_string(),
            "unexpected argument: filename.txt"
        );

        // Test Stdio argument
        let arg = Stdio;
        assert_eq!(
            arg.into_error(None::<&str>).to_string(),
            "unexpected argument: -"
        );
    }

    #[test]
    fn trailing_values() -> Result<()> {
        let mut parser =
            Parser::from_arbitrary(["testbin", "-meow", "--awrff=puppy", "--", "meow"])?;
        while let Some(p) = parser.forward()? {
            dbg!(p);
        }
        Ok(())
    }

    // GNU-style short option tests
    #[test]
    fn short_option_clustering() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "-abc"])?;

        assert_eq!(parser.forward()?, Some(Short('a')));
        assert_eq!(parser.forward()?, Some(Short('b')));
        assert_eq!(parser.forward()?, Some(Short('c')));
        assert!(parser.forward()?.is_none());
        Ok(())
    }

    #[test]
    fn short_option_clustering_with_final_value() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "-abf", "value"])?;

        assert_eq!(parser.forward()?, Some(Short('a')));
        assert_eq!(parser.forward()?, Some(Short('b')));
        assert_eq!(parser.forward()?, Some(Short('f')));
        assert_eq!(parser.forward()?, Some(Value("value".into())));
        assert!(parser.forward()?.is_none());
        Ok(())
    }

    #[test]
    fn short_option_with_separate_value() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "-f", "value"])?;

        assert_eq!(parser.forward()?, Some(Short('f')));
        // Value should be available for consumption if the option expects it
        assert_eq!(parser.forward()?, Some(Value("value".into())));
        assert!(parser.forward()?.is_none());
        Ok(())
    }

    #[test]
    fn clustered_short_options_all_flags() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "-abcd"])?;

        assert_eq!(parser.forward()?, Some(Short('a')));
        assert_eq!(parser.forward()?, Some(Short('b')));
        assert_eq!(parser.forward()?, Some(Short('c')));
        assert_eq!(parser.forward()?, Some(Short('d')));
        assert!(parser.forward()?.is_none());
        Ok(())
    }

    // GNU-style long option tests
    #[test]
    fn long_option_with_equals() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "--file=myfile.txt"])?;

        assert_eq!(parser.forward()?, Some(Long("file")));
        assert_eq!(parser.value().as_deref(), Some("myfile.txt"));
        assert!(parser.forward()?.is_none());
        Ok(())
    }

    #[test]
    fn long_option_with_separate_value() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "--file", "myfile.txt"])?;

        assert_eq!(parser.forward()?, Some(Long("file")));
        assert_eq!(parser.forward()?, Some(Value("myfile.txt".into())));
        assert!(parser.forward()?.is_none());
        Ok(())
    }

    #[test]
    fn long_option_without_value() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "--verbose"])?;

        assert_eq!(parser.forward()?, Some(Long("verbose")));
        assert_eq!(parser.value().as_deref(), None);
        assert!(parser.forward()?.is_none());
        Ok(())
    }

    #[test]
    fn long_option_empty_value() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "--empty="])?;

        assert_eq!(parser.forward()?, Some(Long("empty")));
        assert_eq!(parser.value().as_deref(), Some(""));
        assert!(parser.forward()?.is_none());
        Ok(())
    }

    // Double dash (--) terminator tests
    #[test]
    fn double_dash_terminator() -> Result<()> {
        let mut parser =
            Parser::from_arbitrary(["prog", "--verbose", "--", "--not-an-option", "-x"])?;

        assert_eq!(parser.forward()?, Some(Long("verbose")));
        assert_eq!(parser.forward()?, Some(Value("--not-an-option".into())));
        assert_eq!(parser.forward()?, Some(Value("-x".into())));
        assert!(parser.forward()?.is_none());
        Ok(())
    }

    #[test]
    fn double_dash_alone() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "--"])?;

        assert!(parser.forward()?.is_none());
        Ok(())
    }

    #[test]
    fn double_dash_with_values_only() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "--", "file1", "file2", "file3"])?;

        assert_eq!(parser.forward()?, Some(Value("file1".into())));
        assert_eq!(parser.forward()?, Some(Value("file2".into())));
        assert_eq!(parser.forward()?, Some(Value("file3".into())));
        assert!(parser.forward()?.is_none());
        Ok(())
    }

    // Single dash tests
    #[test]
    fn single_dash_as_stdio() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "-"])?;

        assert_eq!(parser.forward()?, Some(Stdio));
        assert!(parser.forward()?.is_none());
        Ok(())
    }

    #[test]
    fn single_dash_mixed_with_options() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "--verbose", "-", "-x"])?;

        assert_eq!(parser.forward()?, Some(Long("verbose")));
        assert_eq!(parser.forward()?, Some(Stdio));
        assert_eq!(parser.forward()?, Some(Short('x')));
        assert!(parser.forward()?.is_none());
        Ok(())
    }

    #[test]
    fn multiple_stdio_arguments() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "-", "-", "-"])?;

        assert_eq!(parser.forward()?, Some(Stdio));
        assert_eq!(parser.forward()?, Some(Stdio));
        assert_eq!(parser.forward()?, Some(Stdio));
        assert!(parser.forward()?.is_none());
        Ok(())
    }

    #[test]
    fn stdio_with_values_after_double_dash() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "-", "--", "-", "regular_file"])?;

        assert_eq!(parser.forward()?, Some(Stdio));
        assert_eq!(parser.forward()?, Some(Value("-".into())));
        assert_eq!(parser.forward()?, Some(Value("regular_file".into())));
        assert!(parser.forward()?.is_none());
        Ok(())
    }

    // Edge cases and error conditions
    #[test]
    fn empty_long_option() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "--"])?;

        assert!(parser.forward()?.is_none());

        Ok(())
    }

    #[test]
    fn short_option_with_equals_causes_error() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "-x=value"])?;

        assert_eq!(parser.forward()?, Some(Short('x')));

        assert!(parser.forward().is_err());

        Ok(())
    }

    #[test]
    fn numeric_short_options() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "-1", "-2", "-3"])?;

        assert_eq!(parser.forward()?, Some(Short('1')));
        assert_eq!(parser.forward()?, Some(Short('2')));
        assert_eq!(parser.forward()?, Some(Short('3')));
        assert!(parser.forward()?.is_none());
        Ok(())
    }

    #[test]
    fn special_character_short_options() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "-@", "-#", "-%"])?;

        assert_eq!(parser.forward()?, Some(Short('@')));
        assert_eq!(parser.forward()?, Some(Short('#')));
        assert_eq!(parser.forward()?, Some(Short('%')));
        assert!(parser.forward()?.is_none());
        Ok(())
    }

    // Complex scenarios
    #[test]
    fn complex_mixed_arguments() -> Result<()> {
        let mut parser = Parser::from_arbitrary([
            "myprogram",
            "-abc",
            "--verbose",
            "-f",
            "file1.txt",
            "--output=result.txt",
            "--",
            "positional1",
            "--not-parsed-as-option",
            "-also-positional",
        ])?;

        assert_eq!(parser.name(), "myprogram");

        // Clustered short options
        assert_eq!(parser.forward()?, Some(Short('a')));
        assert_eq!(parser.forward()?, Some(Short('b')));
        assert_eq!(parser.forward()?, Some(Short('c')));

        // Long option without value
        assert_eq!(parser.forward()?, Some(Long("verbose")));

        // Short option followed by separate value
        assert_eq!(parser.forward()?, Some(Short('f')));
        assert_eq!(parser.forward()?, Some(Value("file1.txt".into())));

        // Long option with attached value
        assert_eq!(parser.forward()?, Some(Long("output")));
        assert_eq!(parser.value().as_deref(), Some("result.txt"));

        // Everything after -- should be positional
        assert_eq!(parser.forward()?, Some(Value("positional1".into())));
        assert_eq!(
            parser.forward()?,
            Some(Value("--not-parsed-as-option".into()))
        );
        assert_eq!(parser.forward()?, Some(Value("-also-positional".into())));

        assert!(parser.forward()?.is_none());
        Ok(())
    }

    #[test]
    fn program_name_extraction() -> Result<()> {
        let parser1 = Parser::from_arbitrary(["simple"])?;
        assert_eq!(parser1.name(), "simple");

        let parser2 = Parser::from_arbitrary(["/usr/bin/complex-name"])?;
        assert_eq!(parser2.name(), "/usr/bin/complex-name");

        let parser3 = Parser::from_arbitrary(["./relative/path/prog"])?;
        assert_eq!(parser3.name(), "./relative/path/prog");

        Ok(())
    }

    #[test]
    fn unicode_in_options() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "--файл=документ.txt", "-ñ"])?;

        assert_eq!(parser.forward()?, Some(Long("файл")));
        assert_eq!(parser.value().as_deref(), Some("документ.txt"));
        assert_eq!(parser.forward()?, Some(Short('ñ')));
        assert!(parser.forward()?.is_none());
        Ok(())
    }

    #[test]
    fn whitespace_in_values() -> Result<()> {
        let mut parser = Parser::from_arbitrary([
            "prog",
            "--message=hello world",
            "-f",
            "file with spaces.txt",
        ])?;

        assert_eq!(parser.forward()?, Some(Long("message")));
        assert_eq!(parser.value().as_deref(), Some("hello world"));
        assert_eq!(parser.forward()?, Some(Short('f')));
        assert_eq!(
            parser.forward()?,
            Some(Value("file with spaces.txt".into()))
        );
        assert!(parser.forward()?.is_none());
        Ok(())
    }

    #[test]
    fn multiple_equals_in_value() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "--equation=x=y+z=w"])?;

        assert_eq!(parser.forward()?, Some(Long("equation")));
        assert_eq!(parser.value().as_deref(), Some("x=y+z=w"));
        assert!(parser.forward()?.is_none());
        Ok(())
    }

    #[test]
    fn empty_arguments() -> Result<()> {
        let mut parser = Parser::from_arbitrary(["prog", "", "--verbose", ""])?;

        assert_eq!(parser.forward()?, Some(Value("".into())));
        assert_eq!(parser.forward()?, Some(Long("verbose")));
        assert_eq!(parser.forward()?, Some(Value("".into())));
        assert!(parser.forward()?.is_none());
        Ok(())
    }

    // GNU getopt compatibility tests
    #[test]
    fn getopt_style_option_parsing() -> Result<()> {
        // Test POSIX-style where options must come before operands
        let mut parser = Parser::from_arbitrary(["prog", "-a", "operand", "-b"])?;

        assert_eq!(parser.forward()?, Some(Short('a')));
        assert_eq!(parser.forward()?, Some(Value("operand".into())));

        // Depending on GNU vs POSIX mode, -b might be treated as option or operand
        match parser.forward()? {
            Some(Short('b')) => {
                // GNU-style: options can appear anywhere
            }
            Some(Value(val)) if val == "-b" => {
                // POSIX-style: -b is treated as operand after first operand
            }
            other => panic!("Unexpected result: {other:?}"),
        }
        Ok(())
    }

    #[test]
    fn boundary_conditions() -> Result<()> {
        // Test with just program name
        let mut parser1 = Parser::from_arbitrary(["prog"])?;
        assert!(parser1.forward()?.is_none());

        // Test with maximum length option names (if your implementation has limits)
        let long_name = "a".repeat(1000);
        let long_option = format!("--{long_name}");
        let mut parser2 = Parser::from_arbitrary(["prog", &long_option])?;
        if let Some(Long(name)) = parser2.forward()? {
            assert_eq!(name, long_name);
        }

        Ok(())
    }
}
