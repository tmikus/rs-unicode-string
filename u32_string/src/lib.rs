#![feature(const_trait_impl)]
#![feature(extend_one)]
#![feature(pattern)]
#![feature(rustc_attrs)]
#![feature(slice_concat_trait)]
#![feature(slice_range)]
#![feature(specialization)]
#![feature(str_internals)]

use proc_macro::{Delimiter, Group, Literal, Punct, Spacing, TokenStream, TokenTree};
use syn::{parse_macro_input, LitStr};

mod u32_string;
mod u32str;

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
    return [TokenTree::Group(Group::new(Delimiter::Bracket, chars))]
        .into_iter()
        .collect();
}

// pub use self::u32str::*;
