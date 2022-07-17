use u32_string::{u32str, ustr, U32String};

#[test]
fn test_ustr_macro() {
    let value: &u32str = ustr!("hello world");
    assert_eq!(value.to_string(), "hello world");
}

#[test]
fn test_ustring_from() {
    let string = U32String::from("birthday gift");
    let boxed_str = string.clone().into_boxed_u32str();
    let value = boxed_str.into_u32string();
    assert!(value.eq(&string));
}
