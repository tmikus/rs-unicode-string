use u32_string::ustr;

#[test]
fn test_hello_ustr() {
    assert_eq!(
        ustr!("Hello ustr!"),
        ['H', 'e', 'l', 'l', 'o', ' ', 'u', 's', 't', 'r', '!']
    );
}
