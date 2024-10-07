use std::{
    ffi::{OsStr, OsString},
    fmt::Debug,
    os::unix::prelude::OsStrExt,
};

pub enum Error {
    UnexpectedArgument(OsString),
    MissingArgument(&'static str),
    MissingValue(&'static str),
}

impl Debug for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnexpectedArgument(arg) => {
                write!(f, "Found unexpected argument \"{}\"", arg.to_string_lossy())
            }
            Self::MissingArgument(arg) => write!(f, "Argument \"{arg}\" required but not supplied"),
            Self::MissingValue(arg) => write!(f, "No value supplied to \"{arg}\""),
        }
    }
}

pub trait Arg {
    fn is_value(&self) -> bool;
}

impl<T: AsRef<OsStr>> Arg for T {
    #[inline]
    fn is_value(&self) -> bool {
        !self.as_ref().as_bytes().starts_with(b"-")
    }
}

pub trait Parser: Sized {
    const HELP: &'static str;
    const VERSION: &'static str;

    fn try_parse<I>(args: I) -> Result<Self, Error>
    where
        I: IntoIterator<Item = OsString>;
}
