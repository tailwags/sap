#![no_main]

use libfuzzer_sys::fuzz_target;
use sap::Parser;

fuzz_target!(|data: &[u8]| {
    let byte_args: Vec<String> = data.iter().map(|&b| format!("{}", b as char)).collect();
    let mut args = vec!["fuzz"];
    args.extend(byte_args.iter().map(|s| s.as_str()));

    if let Ok(mut parser) = Parser::from_arbitrary(args) {
        while let Ok(Some(_)) = parser.forward() {
            let _ = parser.value();
        }
    }

    let null_string = String::from_utf8_lossy(data);
    let null_split: Vec<&str> = null_string.split('\0').collect();
    let mut args = vec!["fuzz"];
    args.extend(null_split);

    if let Ok(mut parser) = Parser::from_arbitrary(args) {
        while let Ok(Some(_)) = parser.forward() {
            let _ = parser.value();
        }
    }
});
