#![no_main]

use libfuzzer_sys::fuzz_target;
use sap::Parser;

fuzz_target!(|data: &[u8]| {
    let mut args: Vec<String> = vec!["fuzz".to_string()];

    for &byte in data {
        args.push(format!("{}", byte));
        args.push(format!("{:x}", byte));
        args.push(format!("{:b}", byte));
        args.push(format!("{}", byte as char));
        args.push(format!("-{}", byte as char));
        args.push(format!("--{}", byte as char));
        args.push(format!("--{}={}", byte as char, byte));
        args.push(format!("--{}={:x}", byte, byte));
    }

    if let Ok(mut parser) = Parser::from_arbitrary(args) {
        while let Ok(Some(_)) = parser.forward() {
            let _ = parser.value();
        }
    }
});
