#![windows_subsystem = "console"]

use std::ffi::OsString;
use std::os::windows::ffi::OsStringExt;

use sap::args_windows;

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

fn main() {
    let args: Vec<OsString> = std::env::args_os().collect();

    dbg!(args);

    unsafe {
        if !COMMAND_LINE_BUFFER.is_null() {
            let args: Vec<OsString> = args_windows().map(|arg| OsString::from_wide(arg)).collect();

            dbg!(args);

            for arg in args_windows() {
                dbg!(OsString::from_wide(arg));
            }

            dbg!(COMMAND_LINE_BUFFER.to_string());
        }
    }
}
