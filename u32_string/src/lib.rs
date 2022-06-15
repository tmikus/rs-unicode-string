#![feature(const_eval_select)]
#![feature(const_mut_refs)]
#![feature(const_ops)]
#![feature(const_slice_from_raw_parts)]
#![feature(const_slice_ptr_len)]
#![feature(const_trait_impl)]
#![feature(extend_one)]
#![feature(fmt_internals)]
#![feature(hasher_prefixfree_extras)]
#![feature(pattern)]
#![feature(rustc_allow_const_fn_unstable)]
#![feature(rustc_attrs)]
#![feature(slice_concat_trait)]
#![feature(slice_index_methods)]
#![feature(slice_ptr_get)]
#![feature(slice_ptr_len)]
#![feature(slice_range)]
#![feature(specialization)]
#![feature(str_internals)]
#![feature(unicode_internals)]
#![feature(vec_into_raw_parts)]

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
