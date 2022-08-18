#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(not(feature = "std"), feature(unchecked_math))]
// #![deny(unsafe_op_in_unsafe_fn)]

#[cfg(not(feature = "std"))]
use core::ffi::CStr;

#[cfg(feature = "std")]
use std::ffi::CStr;

use static_args::StaticArgs;

pub struct Args {
    inner: StaticArgs,
}

#[derive(Debug)]
pub struct Arg<'a> {
    inner: ArgInner<'a>,
}

#[derive(Debug)]
enum ArgInner<'a> {
    Unicode(&'a str),
    Raw(&'a CStr),
}

impl<'a> ArgInner<'a> {
    pub fn new(raw: &'a CStr) -> Self {
        if let Ok(unicode) = raw.to_str() {
            Self::Unicode(unicode)
        } else {
            Self::Raw(raw)
        }
    }

    pub fn as_bytes(&self) -> &[u8] {
        match self {
            ArgInner::Unicode(unicode) => unicode.as_bytes(),
            ArgInner::Raw(raw) => raw.to_bytes(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.as_bytes().is_empty()
    }

    pub fn is_stdio(&self) -> bool {
        self.as_bytes() == b"-"
    }

    pub fn is_escape(&self) -> bool {
        self.as_bytes() == b"--"
    }

    pub fn is_long(&self) -> bool {
        self.as_bytes().starts_with(b"--") && !self.is_escape()
    }

    pub fn is_short(&self) -> bool {
        self.as_bytes().starts_with(b"-") && !self.is_stdio() && !self.is_long()
    }
}

impl<'a> Arg<'a> {
    pub fn new(inner: &'a CStr) -> Self {
        Self {
            inner: ArgInner::new(inner),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    pub fn is_stdio(&self) -> bool {
        self.inner.is_stdio()
    }

    pub fn is_escape(&self) -> bool {
        self.inner.is_escape()
    }

    pub fn is_long(&self) -> bool {
        self.inner.is_long()
    }

    pub fn is_short(&self) -> bool {
        self.inner.is_short()
    }
}

impl Args {
    pub const fn new(inner: StaticArgs) -> Self {
        Self { inner }
    }
}

impl Iterator for Args {
    type Item = Arg<'static>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(Arg::new)
    }
}

// #[cfg(test)]
// mod test {
//     // FIXME: This test isn't very good because we can't actually pass additional parameters.
//     #[test]
//     fn args_matches_std() {
//         use std::ffi::{OsStr, OsString};

//         let std_args: Vec<OsString> = std::env::args_os().collect();
//         let args: Vec<OsString> = {
//             #[cfg(any(
//                 all(target_os = "linux", target_env = "gnu"),
//                 target_os = "macos",
//                 target_os = "freebsd"
//             ))]
//             {
//                 use std::os::unix::ffi::OsStrExt;

//                 crate::args()
//                     .map(|arg| OsStr::from_bytes(arg.to_bytes()).to_os_string())
//                     .collect()
//             }

//             #[cfg(all(target_os = "windows"))]
//             {
//                 use std::os::windows::ffi::OsStringExt;

//                 crate::args_windows()
//                     .map(|arg| OsString::from_wide(arg))
//                     .collect()
//             }
//         };

//         assert_eq!(std_args, args)
//     }
// }
