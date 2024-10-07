use std::{
    ffi::{OsStr, OsString},
    fmt::Debug,
    os::unix::prelude::OsStrExt,
};

pub use sap_macros::Parser;

#[derive(thiserror::Error)]
pub enum Error {
    #[error("")]
    UnexpectedArgument(OsString),
    #[error("")]
    MissingArgument(&'static str),
    #[error("")]
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

#[inline]
pub fn get_value<T: Arg, V: From<T>>(
    val: Option<T>,
    name: &'static str,
) -> Result<Option<V>, Error> {
    match val {
        Some(arg) if arg.is_value() => Ok(Some(arg.into())),
        _ => return Err(Error::MissingValue(name)),
    }
}

pub trait Parser: Sized {
    const HELP: &'static str;
    const VERSION: &'static str;

    fn try_parse<I>(args: I) -> Result<Self, Error>
    where
        I: IntoIterator<Item = OsString>;
}
