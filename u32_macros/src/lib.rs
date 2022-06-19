#![feature(proc_macro_quote)]

use proc_macro::{
    quote, Delimiter, Group, Ident, Literal, Punct, Spacing, Span, TokenStream, TokenTree,
};
use syn::{parse_macro_input, LitStr};

#[proc_macro]
pub fn ustr(input: TokenStream) -> TokenStream {
    let input = dbg!(input);
    let result = parse_macro_input!(input as LitStr);
    let chars = result
        .value()
        .chars()
        .into_iter()
        .flat_map(|c| {
            [
                TokenTree::Literal(Literal::character(c)),
                TokenTree::Punct(Punct::new(',', Spacing::Alone)),
            ]
        })
        .collect();
    let chars_array = TokenTree::Group(Group::new(Delimiter::Bracket, chars));
    let params: TokenStream = [chars_array].into_iter().collect();
    let expanded = quote! {
        unsafe {
            // let result: &::u32_string::u32str = ::std::mem::transmute($params);
            // result
            &::u32_string::u32str {
                data: ($params).as_ptr(),
            }
        }
    };
    dbg!(expanded.into())
    // return [
    //     TokenTree::Ident(Ident::new("u32_string", Span::call_site())),
    //     TokenTree::Punct(Punct::new(':', Spacing::Joint)),
    //     TokenTree::Punct(Punct::new(':', Spacing::Alone)),
    //     TokenTree::Ident(Ident::new("u32str", Span::call_site())),
    //     TokenTree::Punct(Punct::new(':', Spacing::Joint)),
    //     TokenTree::Punct(Punct::new(':', Spacing::Alone)),
    //     TokenTree::Ident(Ident::new("from", Span::call_site())),
    //     TokenTree::Group(Group::new(Delimiter::Parenthesis, params)),
    // ]
    // .into_iter()
    // .collect();
}

// pub use self::u32str::*;
