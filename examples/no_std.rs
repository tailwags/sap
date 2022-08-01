#![feature(lang_items)] // We neeed to enable this to define the `eh_personality`
#![no_std]
#![no_main]

#[no_mangle]
// Notice how we don't need to pass argc or argv.

pub extern "C" fn main() -> isize {
    for arg in sap::args() {
        unsafe {
            libc::printf("%s\n\0".as_ptr().cast(), arg.as_ptr());
        }
    }

    0
}

// Below we define the required language items

#[panic_handler]
fn panic(_panic_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[lang = "eh_personality"]
extern "C" fn eh_personality() {}
