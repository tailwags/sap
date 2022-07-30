#![windows_subsystem = "console"]

#[cfg(all(target_os = "windows", target_env = "msvc"))]
use core::{
    arch::asm,
    ptr::{null, null_mut},
};

#[cfg(all(target_os = "windows", target_env = "msvc"))]
use windows::{
    core::PWSTR,
    Win32::System::{LibraryLoader::GetModuleFileNameW, Threading::PEB},
};

#[cfg(all(target_os = "windows", target_env = "msvc"))]
static mut ARGS: PWSTR = PWSTR(null_mut());

#[cfg(all(target_os = "windows", target_env = "msvc"))]
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

        unsafe { ARGS = (*(*peb).ProcessParameters).CommandLine.Buffer }
    }
    init_args
};

fn main() {
    for argument in std::env::args_os() {
        println!("{argument:?}");
    }

    for arg in sap::args() {
        dbg!(arg);
    }

    #[cfg(all(target_os = "windows", target_env = "msvc"))]
    unsafe {
        if !ARGS.is_null() {
            dbg!(ARGS.to_string().unwrap());
        }

        let mut buf = [0u16; 512];
        GetModuleFileNameW(None, &mut buf);

        dbg!(PWSTR::from_raw(buf.as_mut_ptr()).to_string().unwrap());
    }
}
