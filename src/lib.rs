#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(not(feature = "std"), feature(unchecked_math))]
// #![deny(unsafe_op_in_unsafe_fn)]

#[cfg(not(feature = "std"))]
use core::{
    ffi::{c_char, c_int, CStr},
    ptr::null,
};

#[cfg(feature = "std")]
use std::{
    ffi::CStr,
    os::raw::{c_char, c_int},
    ptr::null,
};

pub mod win32;

pub struct Args {
    next: *const *const c_char,
    end: *const *const c_char,
}

impl Args {
    pub const fn empty() -> Self {
        Self {
            next: null(),
            end: null(),
        }
    }

    /// # Safety
    /// TODO
    pub const unsafe fn new(argc: c_int, argv: *const *const c_char) -> Self {
        Self {
            next: argv,
            end: argv.offset(argc as isize),
        }
    }
}

impl Iterator for Args {
    type Item = &'static CStr;

    fn next(&mut self) -> Option<Self::Item> {
        if self.next == self.end {
            None
        } else {
            let c_str = unsafe { CStr::from_ptr(*self.next) };
            self.next = unsafe { self.next.offset(1) };
            Some(c_str)
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }
}

impl ExactSizeIterator for Args {
    fn len(&self) -> usize {
        #[cfg(feature = "std")]
        {
            self.end as usize - self.next as usize
        }
        #[cfg(not(feature = "std"))]
        unsafe {
            // FIXME: Requires stabilization of unchecked_math. see rust-lang/rust#85122
            (self.end as usize).unchecked_sub(self.next as usize)
        }
    }
}

static mut ARGC: c_int = 0;
static mut ARGV: *const *const c_char = null();

#[cfg(any(all(target_os = "linux", target_env = "gnu"), target_os = "macos"))]
#[cfg_attr(target_os = "linux", link_section = ".init_array")]
#[cfg_attr(target_os = "macos", link_section = "__DATA,__mod_init_func")]
#[used]
static ARGV_INIT_ARRAY: extern "C" fn(c_int, *const *const c_char, *const *const c_char) = {
    extern "C" fn init_wrapper(
        argc: c_int,
        argv: *const *const c_char,
        _envp: *const *const c_char,
    ) {
        unsafe {
            ARGC = argc;
            ARGV = argv;
        }
    }
    init_wrapper
};

// #[must_use]
pub fn args() -> Args {
    unsafe {
        if ARGV.is_null() {
            Args::empty()
        } else {
            Args::new(ARGC, ARGV)
        }
    }
}

#[cfg(all(target_os = "windows", target_env = "msvc"))]
pub fn args_windows() -> win32::Args<'static> {
    use core::{arch::asm, ptr::null_mut};
    use windows::{core::PWSTR, Win32::System::Threading::PEB};

    static mut COMMAND_LINE_BUFFER: PWSTR = PWSTR(null_mut());

    #[used]
    #[link_section = ".CRT$XCU"]
    static ARGS_INIT: extern "C" fn() = {
        extern "C" fn init_args() {
            let peb: *mut PEB;
            unsafe {
                asm!(
                  "mov {}, gs:[0x60]",
                  out(reg) peb,
                  options(pure, nomem, nostack)
                );
            }

            unsafe { COMMAND_LINE_BUFFER = (*(*peb).ProcessParameters).CommandLine.Buffer }
        }
        init_args
    };

    if unsafe { COMMAND_LINE_BUFFER.is_null() } {
        win32::Args::empty()
    } else {
        unsafe { win32::Args::new(COMMAND_LINE_BUFFER.as_wide()) }
    }
}

#[cfg(test)]
mod test {

    // FIXME: This test isn't very good because we can't actually pass additional parameters.
    #[cfg(any(all(target_os = "linux", target_env = "gnu"), target_os = "macos"))]
    #[test]
    fn args_matches_std() {
        use std::{
            ffi::{OsStr, OsString},
            os::unix::ffi::OsStrExt,
        };

        let std_args: Vec<OsString> = std::env::args_os().collect();
        let args: Vec<OsString> = crate::args()
            .map(|arg| OsStr::from_bytes(arg.to_bytes()).to_os_string())
            .collect();

        assert_eq!(std_args, args)
    }
}
