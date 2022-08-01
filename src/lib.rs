#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(not(feature = "std"), feature(unchecked_math))]
// #![deny(unsafe_op_in_unsafe_fn)]

#[cfg(any(all(target_os = "linux", target_env = "gnu"), target_os = "macos"))]
mod unix;
#[cfg(all(target_os = "windows", target_env = "msvc"))]
mod win32;

#[cfg(any(all(target_os = "linux", target_env = "gnu"), target_os = "macos"))]
pub use unix::*;
#[cfg(all(target_os = "windows", target_env = "msvc"))]
pub use win32::*;

#[cfg(test)]
mod test {
    // FIXME: This test isn't very good because we can't actually pass additional parameters.
    #[test]
    fn args_matches_std() {
        use std::ffi::{OsStr, OsString};

        let std_args: Vec<OsString> = std::env::args_os().collect();
        let args: Vec<OsString> = {
            #[cfg(any(all(target_os = "linux", target_env = "gnu"), target_os = "macos"))]
            {
                use std::os::unix::ffi::OsStrExt;

                crate::args()
                    .map(|arg| OsStr::from_bytes(arg.to_bytes()).to_os_string())
                    .collect()
            }

            #[cfg(all(target_os = "windows", target_env = "msvc"))]
            {
                use std::os::windows::ffi::OsStringExt;

                crate::args_windows()
                    .map(|arg| OsString::from_wide(arg))
                    .collect()
            }
        };

        assert_eq!(std_args, args)
    }
}
