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
#![feature(allocator_api)]

mod u32str_impl;
mod u32string_impl;

pub use self::u32str_impl::*;
pub use self::u32string_impl::*;
pub use u32_macros::*;
