#![cfg_attr(not(feature = "std"), feature(lang_items))] // We neeed to enable this to define the `eh_personality`
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(not(feature = "std"), no_main)]

#[cfg(not(feature = "std"))]
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

#[cfg(not(feature = "std"))]
#[panic_handler]
fn panic(_panic_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[cfg(not(feature = "std"))]
#[lang = "eh_personality"]
extern "C" fn eh_personality() {}

#[cfg(feature = "std")]
fn main() {
    panic!("Tried to run this example on stable and/or without disabling std")
}
