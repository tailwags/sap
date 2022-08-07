use sap_macros::utf16_string;

#[test]
fn is_valid_utf16() {
    let known_good: Vec<u16> = "This is an example string".encode_utf16().collect();
    let constructed = utf16_string!("This is an example string");

    assert_eq!(&known_good, &constructed);
}
