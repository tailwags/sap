use std::{ffi::OsString, fmt::Debug, os::unix::prelude::OsStrExt};

pub enum Error {
    UnexpectedArgument(&'static str),
    MissingArgument(&'static str),
    MissingValue(&'static str),
}

impl Debug for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnexpectedArgument(arg) => write!(f, "Found unexpected argument \"{arg}\""),
            Self::MissingArgument(arg) => write!(f, "Argument \"{arg}\" required but not supplied"),
            Self::MissingValue(arg) => write!(f, "No value supplied to \"{arg}\""),
        }
    }
}

#[derive(Debug)]
pub enum Arg<'a> {
    Short(&'a [u8]),
    Long(&'a [u8]),
    Value(OsString),
}

impl<'a> Arg<'a> {
    pub fn expect_value(self) -> Option<OsString> {
        if let Self::Value(value) = self {
            Some(value)
        } else {
            None
        }
    }
}

pub trait ParseArg {
    fn parse(&self) -> Arg;
}

impl ParseArg for OsString {
    fn parse(&self) -> Arg {
        if let Some(arg) = self.as_bytes().strip_prefix(b"--") {
            Arg::Long(arg)
        } else if let Some(arg) = self.as_bytes().strip_prefix(b"-") {
            Arg::Short(arg)
        } else {
            Arg::Value(self.to_os_string())
        }
    }
}
