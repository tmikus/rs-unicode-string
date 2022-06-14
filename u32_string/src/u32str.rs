// Many of the usings in this module are only used in the test configuration.
// It's cleaner to just turn off the unused_imports warning than to fix them.
#![allow(unused_imports)]

//! Unicode string slices.
//!
//! *[See also the `str` primitive type](str).*
//!
//! The `&str` type is one of the two main string types, the other being `String`.
//! Unlike its `String` counterpart, its contents are borrowed.
//!
//! # Basic Usage
//!
//! A basic string declaration of `&str` type:
//!
//! ```
//! let hello_world = "Hello, World!";
//! ```
//!
//! Here we have declared a string literal, also known as a string slice.
//! String literals have a static lifetime, which means the string `hello_world`
//! is guaranteed to be valid for the duration of the entire program.
//! We can explicitly specify `hello_world`'s lifetime as well:
//!
//! ```
//! let hello_world: &'static str = "Hello, world!";
//! ```
pub struct u32str {
    // Raw pointer because it's easier for the users not to have to deal with the lifecycles
    // of the u32str type
    pub(crate) data: [char],
}

use core::borrow::{Borrow, BorrowMut};
use core::iter::FusedIterator;
use core::mem;
use core::ptr;
use core::str::pattern::{DoubleEndedSearcher, Pattern, ReverseSearcher, Searcher};
use core::unicode::conversions;

use std::borrow::ToOwned;
use std::boxed::Box;
use std::ops;
use std::slice::{Concat, Join, SliceIndex};
use std::string::String;
use std::vec::Vec;

pub use core::str::pattern;
pub use core::str::EncodeUtf16;
pub use core::str::SplitAsciiWhitespace;
pub use core::str::SplitInclusive;
pub use core::str::SplitWhitespace;
pub use core::str::{from_utf8, from_utf8_mut, Bytes, CharIndices, Chars};
// pub use core::str::{from_utf8_unchecked, from_utf8_unchecked_mut, ParseBoolError};
pub use core::str::{EscapeDebug, EscapeDefault, EscapeUnicode};
pub use core::str::{FromStr, Utf8Error};
#[allow(deprecated)]
pub use core::str::{Lines, LinesAny};
pub use core::str::{MatchIndices, RMatchIndices};
pub use core::str::{Matches, RMatches};
pub use core::str::{RSplit, Split};
pub use core::str::{RSplitN, SplitN};
pub use core::str::{RSplitTerminator, SplitTerminator};
use proc_macro::TokenStream;

use crate::u32_string::U32String;

/// Note: `str` in `Concat<str>` is not meaningful here.
/// This type parameter of the trait only exists to enable another impl.
#[cfg(not(no_global_oom_handling))]
impl<S: Borrow<u32str>> Concat<u32str> for [S] {
    type Output = U32String;

    fn concat(slice: &Self) -> U32String {
        let data: [char; 0] = [];
        Join::join(
            slice,
            &u32str {
                data: data as [char],
            },
        )
    }
}

#[cfg(not(no_global_oom_handling))]
impl<S: Borrow<u32str>> Join<&u32str> for [S] {
    type Output = U32String;

    fn join(slice: &Self, sep: &u32str) -> U32String {
        unsafe { U32String::from_utf8_unchecked(join_generic_copy(slice, sep.as_bytes())) }
    }
}

impl ops::Index<ops::Range<usize>> for u32str {
    type Output = u32str;

    #[inline]
    fn index(&self, index: ops::Range<usize>) -> &u32str {
        &self[..][index]
    }
}
impl ops::Index<ops::RangeTo<usize>> for u32str {
    type Output = u32str;

    #[inline]
    fn index(&self, index: ops::RangeTo<usize>) -> &u32str {
        &self[..][index]
    }
}
impl ops::Index<ops::RangeFrom<usize>> for u32str {
    type Output = u32str;

    #[inline]
    fn index(&self, index: ops::RangeFrom<usize>) -> &u32str {
        &self[..][index]
    }
}
impl ops::Index<ops::RangeFull> for u32str {
    type Output = u32str;

    #[inline]
    fn index(&self, _index: ops::RangeFull) -> &u32str {
        unsafe { u32str::from_utf8_unchecked(&self.vec) }
    }
}
impl ops::Index<ops::RangeInclusive<usize>> for u32str {
    type Output = u32str;

    #[inline]
    fn index(&self, index: ops::RangeInclusive<usize>) -> &u32str {
        ops::Index::index(&**self, index)
    }
}
impl ops::Index<ops::RangeToInclusive<usize>> for u32str {
    type Output = u32str;

    #[inline]
    fn index(&self, index: ops::RangeToInclusive<usize>) -> &u32str {
        ops::Index::index(&**self, index)
    }
}

impl ops::IndexMut<ops::Range<usize>> for u32str {
    #[inline]
    fn index_mut(&mut self, index: ops::Range<usize>) -> &mut u32str {
        &mut self[..][index]
    }
}
impl ops::IndexMut<ops::RangeTo<usize>> for u32str {
    #[inline]
    fn index_mut(&mut self, index: ops::RangeTo<usize>) -> &mut u32str {
        &mut self[..][index]
    }
}
impl ops::IndexMut<ops::RangeFrom<usize>> for u32str {
    #[inline]
    fn index_mut(&mut self, index: ops::RangeFrom<usize>) -> &mut u32str {
        &mut self[..][index]
    }
}
impl ops::IndexMut<ops::RangeFull> for u32str {
    #[inline]
    fn index_mut(&mut self, _index: ops::RangeFull) -> &mut u32str {
        unsafe { u32str::from_utf8_unchecked_mut(&mut *self.vec) }
    }
}
impl ops::IndexMut<ops::RangeInclusive<usize>> for u32str {
    #[inline]
    fn index_mut(&mut self, index: ops::RangeInclusive<usize>) -> &mut u32str {
        ops::IndexMut::index_mut(&mut **self, index)
    }
}
impl ops::IndexMut<ops::RangeToInclusive<usize>> for u32str {
    #[inline]
    fn index_mut(&mut self, index: ops::RangeToInclusive<usize>) -> &mut u32str {
        ops::IndexMut::index_mut(&mut **self, index)
    }
}

#[cfg(not(no_global_oom_handling))]
macro_rules! specialize_for_lengths {
    ($separator:expr, $target:expr, $iter:expr; $($num:expr),*) => {{
        let mut target = $target;
        let iter = $iter;
        let sep_bytes = $separator;
        match $separator.len() {
            $(
                // loops with hardcoded sizes run much faster
                // specialize the cases with small separator lengths
                $num => {
                    for s in iter {
                        copy_slice_and_advance!(target, sep_bytes);
                        let content_bytes = s.borrow().as_ref();
                        copy_slice_and_advance!(target, content_bytes);
                    }
                },
            )*
            _ => {
                // arbitrary non-zero size fallback
                for s in iter {
                    copy_slice_and_advance!(target, sep_bytes);
                    let content_bytes = s.borrow().as_ref();
                    copy_slice_and_advance!(target, content_bytes);
                }
            }
        }
        target
    }}
}

#[cfg(not(no_global_oom_handling))]
macro_rules! copy_slice_and_advance {
    ($target:expr, $bytes:expr) => {
        let len = $bytes.len();
        let (head, tail) = { $target }.split_at_mut(len);
        head.copy_from_slice($bytes);
        $target = tail;
    };
}

// Optimized join implementation that works for both Vec<T> (T: Copy) and String's inner vec
// Currently (2018-05-13) there is a bug with type inference and specialization (see issue #36262)
// For this reason SliceConcat<T> is not specialized for T: Copy and SliceConcat<str> is the
// only user of this function. It is left in place for the time when that is fixed.
//
// the bounds for String-join are S: Borrow<str> and for Vec-join Borrow<[T]>
// [T] and str both impl AsRef<[T]> for some T
// => s.borrow().as_ref() and we always have slices
#[cfg(not(no_global_oom_handling))]
fn join_generic_copy<B, T, S>(slice: &[S], sep: &[T]) -> Vec<T>
where
    T: Copy,
    B: AsRef<[T]> + ?Sized,
    S: Borrow<B>,
{
    let sep_len = sep.len();
    let mut iter = slice.iter();

    // the first slice is the only one without a separator preceding it
    let first = match iter.next() {
        Some(first) => first,
        None => return vec![],
    };

    // compute the exact total length of the joined Vec
    // if the `len` calculation overflows, we'll panic
    // we would have run out of memory anyway and the rest of the function requires
    // the entire Vec pre-allocated for safety
    let reserved_len = sep_len
        .checked_mul(iter.len())
        .and_then(|n| {
            slice
                .iter()
                .map(|s| s.borrow().as_ref().len())
                .try_fold(n, usize::checked_add)
        })
        .expect("attempt to join into collection with len > usize::MAX");

    // prepare an uninitialized buffer
    let mut result = Vec::with_capacity(reserved_len);
    debug_assert!(result.capacity() >= reserved_len);

    result.extend_from_slice(first.borrow().as_ref());

    unsafe {
        let pos = result.len();
        let target = result
            .spare_capacity_mut()
            .get_unchecked_mut(..reserved_len - pos);

        // Convert the separator and slices to slices of MaybeUninit
        // to simplify implementation in specialize_for_lengths
        let sep_uninit = core::slice::from_raw_parts(sep.as_ptr().cast(), sep.len());
        let iter_uninit = iter.map(|it| {
            let it = it.borrow().as_ref();
            core::slice::from_raw_parts(it.as_ptr().cast(), it.len())
        });

        // copy separator and slices over without bounds checks
        // generate loops with hardcoded offsets for small separators
        // massive improvements possible (~ x2)
        let remain = specialize_for_lengths!(sep_uninit, target, iter_uninit; 0, 1, 2, 3, 4);

        // A weird borrow implementation may return different
        // slices for the length calculation and the actual copy.
        // Make sure we don't expose uninitialized bytes to the caller.
        let result_len = reserved_len - remain.len();
        result.set_len(result_len);
    }
    result
}

impl Borrow<u32str> for U32String {
    #[inline]
    fn borrow(&self) -> &u32str {
        &self[..]
    }
}

impl BorrowMut<u32str> for U32String {
    #[inline]
    fn borrow_mut(&mut self) -> &mut u32str {
        &mut self[..]
    }
}

#[cfg(not(no_global_oom_handling))]
impl ToOwned for u32str {
    type Owned = U32String;

    #[inline]
    fn to_owned(&self) -> U32String {
        unsafe { U32String::from_utf8_unchecked(self.as_bytes().to_owned()) }
    }

    fn clone_into(&self, target: &mut U32String) {
        let mut b = mem::take(target).into_bytes();
        self.as_bytes().clone_into(&mut b);
        *target = unsafe { U32String::from_utf8_unchecked(b) }
    }
}

/// Methods for string slices.
#[cfg(not(test))]
impl u32str {
    // /// Converts a `Box<str>` into a `Box<[u8]>` without copying or allocating.
    // ///
    // /// # Examples
    // ///
    // /// Basic usage:
    // ///
    // /// ```
    // /// let s = "this is a string";
    // /// let boxed_str = s.to_owned().into_boxed_str();
    // /// let boxed_bytes = boxed_str.into_boxed_bytes();
    // /// assert_eq!(*boxed_bytes, *s.as_bytes());
    // /// ```
    // #[rustc_allow_incoherent_impl]
    // #[must_use = "`self` will be dropped if the result is not used"]
    // #[inline]
    // pub fn into_boxed_bytes(self: Box<str>) -> Box<[u8]> {
    //     self.into()
    // }

    // /// Replaces all matches of a pattern with another string.
    // ///
    // /// `replace` creates a new [`String`], and copies the data from this string slice into it.
    // /// While doing so, it attempts to find matches of a pattern. If it finds any, it
    // /// replaces them with the replacement string slice.
    // ///
    // /// # Examples
    // ///
    // /// Basic usage:
    // ///
    // /// ```
    // /// let s = "this is old";
    // ///
    // /// assert_eq!("this is new", s.replace("old", "new"));
    // /// assert_eq!("than an old", s.replace("is", "an"));
    // /// ```
    // ///
    // /// When the pattern doesn't match:
    // ///
    // /// ```
    // /// let s = "this is old";
    // /// assert_eq!(s, s.replace("cookie monster", "little lamb"));
    // /// ```
    // #[cfg(not(no_global_oom_handling))]
    // #[rustc_allow_incoherent_impl]
    // #[must_use = "this returns the replaced string as a new allocation, \
    //               without modifying the original"]
    // #[inline]
    // pub fn replace<'a, P: Pattern<'a>>(&'a self, from: P, to: &u32str) -> U32String {
    //     let mut result = String::new();
    //     let mut last_end = 0;
    //     for (start, part) in self.match_indices(from) {
    //         result.push_str(unsafe { self.get_unchecked(last_end..start) });
    //         result.push_str(to);
    //         last_end = start + part.len();
    //     }
    //     result.push_str(unsafe { self.get_unchecked(last_end..self.len()) });
    //     result
    // }

    // /// Replaces first N matches of a pattern with another string.
    // ///
    // /// `replacen` creates a new [`String`], and copies the data from this string slice into it.
    // /// While doing so, it attempts to find matches of a pattern. If it finds any, it
    // /// replaces them with the replacement string slice at most `count` times.
    // ///
    // /// # Examples
    // ///
    // /// Basic usage:
    // ///
    // /// ```
    // /// let s = "foo foo 123 foo";
    // /// assert_eq!("new new 123 foo", s.replacen("foo", "new", 2));
    // /// assert_eq!("faa fao 123 foo", s.replacen('o', "a", 3));
    // /// assert_eq!("foo foo new23 foo", s.replacen(char::is_numeric, "new", 1));
    // /// ```
    // ///
    // /// When the pattern doesn't match:
    // ///
    // /// ```
    // /// let s = "this is old";
    // /// assert_eq!(s, s.replacen("cookie monster", "little lamb", 10));
    // /// ```
    // #[cfg(not(no_global_oom_handling))]
    // #[rustc_allow_incoherent_impl]
    // #[must_use = "this returns the replaced string as a new allocation, \
    //               without modifying the original"]
    // pub fn replacen<'a, P: Pattern<'a>>(&'a self, pat: P, to: &str, count: usize) -> String {
    //     // Hope to reduce the times of re-allocation
    //     let mut result = String::with_capacity(32);
    //     let mut last_end = 0;
    //     for (start, part) in self.match_indices(pat).take(count) {
    //         result.push_str(unsafe { self.get_unchecked(last_end..start) });
    //         result.push_str(to);
    //         last_end = start + part.len();
    //     }
    //     result.push_str(unsafe { self.get_unchecked(last_end..self.len()) });
    //     result
    // }

    // /// Returns the lowercase equivalent of this string slice, as a new [`String`].
    // ///
    // /// 'Lowercase' is defined according to the terms of the Unicode Derived Core Property
    // /// `Lowercase`.
    // ///
    // /// Since some characters can expand into multiple characters when changing
    // /// the case, this function returns a [`String`] instead of modifying the
    // /// parameter in-place.
    // ///
    // /// # Examples
    // ///
    // /// Basic usage:
    // ///
    // /// ```
    // /// let s = "HELLO";
    // ///
    // /// assert_eq!("hello", s.to_lowercase());
    // /// ```
    // ///
    // /// A tricky example, with sigma:
    // ///
    // /// ```
    // /// let sigma = "Σ";
    // ///
    // /// assert_eq!("σ", sigma.to_lowercase());
    // ///
    // /// // but at the end of a word, it's ς, not σ:
    // /// let odysseus = "ὈΔΥΣΣΕΎΣ";
    // ///
    // /// assert_eq!("ὀδυσσεύς", odysseus.to_lowercase());
    // /// ```
    // ///
    // /// Languages without case are not changed:
    // ///
    // /// ```
    // /// let new_year = "农历新年";
    // ///
    // /// assert_eq!(new_year, new_year.to_lowercase());
    // /// ```
    // #[cfg(not(no_global_oom_handling))]
    // #[rustc_allow_incoherent_impl]
    // #[must_use = "this returns the lowercase string as a new String, \
    //               without modifying the original"]
    // pub fn to_lowercase(&self) -> U32String {
    //     let out = convert_while_ascii(self.as_bytes(), u8::to_ascii_lowercase);
    //
    //     // Safety: we know this is a valid char boundary since
    //     // out.len() is only progressed if ascii bytes are found
    //     let rest = unsafe { self.get_unchecked(out.len()..) };
    //
    //     // Safety: We have written only valid ASCII to our vec
    //     let mut s = unsafe { String::from_utf8_unchecked(out) };
    //
    //     for (i, c) in rest[..].char_indices() {
    //         if c == 'Σ' {
    //             // Σ maps to σ, except at the end of a word where it maps to ς.
    //             // This is the only conditional (contextual) but language-independent mapping
    //             // in `SpecialCasing.txt`,
    //             // so hard-code it rather than have a generic "condition" mechanism.
    //             // See https://github.com/rust-lang/rust/issues/26035
    //             map_uppercase_sigma(rest, i, &mut s)
    //         } else {
    //             match conversions::to_lower(c) {
    //                 [a, '\0', _] => s.push(a),
    //                 [a, b, '\0'] => {
    //                     s.push(a);
    //                     s.push(b);
    //                 }
    //                 [a, b, c] => {
    //                     s.push(a);
    //                     s.push(b);
    //                     s.push(c);
    //                 }
    //             }
    //         }
    //     }
    //     return s;
    //
    //     fn map_uppercase_sigma(from: &str, i: usize, to: &mut String) {
    //         // See https://www.unicode.org/versions/Unicode7.0.0/ch03.pdf#G33992
    //         // for the definition of `Final_Sigma`.
    //         debug_assert!('Σ'.len_utf8() == 2);
    //         let is_word_final = case_ignoreable_then_cased(from[..i].chars().rev())
    //             && !case_ignoreable_then_cased(from[i + 2..].chars());
    //         to.push_str(if is_word_final { "ς" } else { "σ" });
    //     }
    //
    //     fn case_ignoreable_then_cased<I: Iterator<Item = char>>(iter: I) -> bool {
    //         use core::unicode::{Case_Ignorable, Cased};
    //         match iter.skip_while(|&c| Case_Ignorable(c)).next() {
    //             Some(c) => Cased(c),
    //             None => false,
    //         }
    //     }
    // }
    //
    // /// Returns the uppercase equivalent of this string slice, as a new [`String`].
    // ///
    // /// 'Uppercase' is defined according to the terms of the Unicode Derived Core Property
    // /// `Uppercase`.
    // ///
    // /// Since some characters can expand into multiple characters when changing
    // /// the case, this function returns a [`String`] instead of modifying the
    // /// parameter in-place.
    // ///
    // /// # Examples
    // ///
    // /// Basic usage:
    // ///
    // /// ```
    // /// let s = "hello";
    // ///
    // /// assert_eq!("HELLO", s.to_uppercase());
    // /// ```
    // ///
    // /// Scripts without case are not changed:
    // ///
    // /// ```
    // /// let new_year = "农历新年";
    // ///
    // /// assert_eq!(new_year, new_year.to_uppercase());
    // /// ```
    // ///
    // /// One character can become multiple:
    // /// ```
    // /// let s = "tschüß";
    // ///
    // /// assert_eq!("TSCHÜSS", s.to_uppercase());
    // /// ```
    // #[cfg(not(no_global_oom_handling))]
    // #[rustc_allow_incoherent_impl]
    // #[must_use = "this returns the uppercase string as a new String, \
    //               without modifying the original"]
    // pub fn to_uppercase(&self) -> String {
    //     let out = convert_while_ascii(self.as_bytes(), u8::to_ascii_uppercase);
    //
    //     // Safety: we know this is a valid char boundary since
    //     // out.len() is only progressed if ascii bytes are found
    //     let rest = unsafe { self.get_unchecked(out.len()..) };
    //
    //     // Safety: We have written only valid ASCII to our vec
    //     let mut s = unsafe { String::from_utf8_unchecked(out) };
    //
    //     for c in rest.chars() {
    //         match conversions::to_upper(c) {
    //             [a, '\0', _] => s.push(a),
    //             [a, b, '\0'] => {
    //                 s.push(a);
    //                 s.push(b);
    //             }
    //             [a, b, c] => {
    //                 s.push(a);
    //                 s.push(b);
    //                 s.push(c);
    //             }
    //         }
    //     }
    //     s
    // }
    //
    // /// Converts a [`Box<str>`] into a [`String`] without copying or allocating.
    // ///
    // /// # Examples
    // ///
    // /// Basic usage:
    // ///
    // /// ```
    // /// let string = String::from("birthday gift");
    // /// let boxed_str = string.clone().into_boxed_str();
    // ///
    // /// assert_eq!(boxed_str.into_string(), string);
    // /// ```
    // #[rustc_allow_incoherent_impl]
    // #[must_use = "`self` will be dropped if the result is not used"]
    // #[inline]
    // pub fn into_string(self: Box<str>) -> String {
    //     let slice = Box::<[u8]>::from(self);
    //     unsafe { String::from_utf8_unchecked(slice.into_vec()) }
    // }
    //
    // /// Creates a new [`String`] by repeating a string `n` times.
    // ///
    // /// # Panics
    // ///
    // /// This function will panic if the capacity would overflow.
    // ///
    // /// # Examples
    // ///
    // /// Basic usage:
    // ///
    // /// ```
    // /// assert_eq!("abc".repeat(4), String::from("abcabcabcabc"));
    // /// ```
    // ///
    // /// A panic upon overflow:
    // ///
    // /// ```should_panic
    // /// // this will panic at runtime
    // /// let huge = "0123456789abcdef".repeat(usize::MAX);
    // /// ```
    // #[cfg(not(no_global_oom_handling))]
    // #[rustc_allow_incoherent_impl]
    // #[must_use]
    // pub fn repeat(&self, n: usize) -> String {
    //     unsafe { String::from_utf8_unchecked(self.as_bytes().repeat(n)) }
    // }
    //
    // /// Returns a copy of this string where each character is mapped to its
    // /// ASCII upper case equivalent.
    // ///
    // /// ASCII letters 'a' to 'z' are mapped to 'A' to 'Z',
    // /// but non-ASCII letters are unchanged.
    // ///
    // /// To uppercase the value in-place, use [`make_ascii_uppercase`].
    // ///
    // /// To uppercase ASCII characters in addition to non-ASCII characters, use
    // /// [`to_uppercase`].
    // ///
    // /// # Examples
    // ///
    // /// ```
    // /// let s = "Grüße, Jürgen ❤";
    // ///
    // /// assert_eq!("GRüßE, JüRGEN ❤", s.to_ascii_uppercase());
    // /// ```
    // ///
    // /// [`make_ascii_uppercase`]: str::make_ascii_uppercase
    // /// [`to_uppercase`]: #method.to_uppercase
    // #[cfg(not(no_global_oom_handling))]
    // #[rustc_allow_incoherent_impl]
    // #[must_use = "to uppercase the value in-place, use `make_ascii_uppercase()`"]
    // #[inline]
    // pub fn to_ascii_uppercase(&self) -> String {
    //     let mut bytes = self.as_bytes().to_vec();
    //     bytes.make_ascii_uppercase();
    //     // make_ascii_uppercase() preserves the UTF-8 invariant.
    //     unsafe { String::from_utf8_unchecked(bytes) }
    // }

    // /// Returns a copy of this string where each character is mapped to its
    // /// ASCII lower case equivalent.
    // ///
    // /// ASCII letters 'A' to 'Z' are mapped to 'a' to 'z',
    // /// but non-ASCII letters are unchanged.
    // ///
    // /// To lowercase the value in-place, use [`make_ascii_lowercase`].
    // ///
    // /// To lowercase ASCII characters in addition to non-ASCII characters, use
    // /// [`to_lowercase`].
    // ///
    // /// # Examples
    // ///
    // /// ```
    // /// let s = "Grüße, Jürgen ❤";
    // ///
    // /// assert_eq!("grüße, jürgen ❤", s.to_ascii_lowercase());
    // /// ```
    // ///
    // /// [`make_ascii_lowercase`]: str::make_ascii_lowercase
    // /// [`to_lowercase`]: #method.to_lowercase
    // #[cfg(not(no_global_oom_handling))]
    // #[rustc_allow_incoherent_impl]
    // #[must_use = "to lowercase the value in-place, use `make_ascii_lowercase()`"]
    // #[inline]
    // pub fn to_ascii_lowercase(&self) -> String {
    //     let mut bytes = self.as_bytes().to_vec();
    //     bytes.make_ascii_lowercase();
    //     // make_ascii_lowercase() preserves the UTF-8 invariant.
    //     unsafe { String::from_utf8_unchecked(bytes) }
    // }

    // /// Converts a slice of bytes to a string slice.
    // ///
    // /// A string slice ([`&str`]) is made of bytes ([`u8`]), and a byte slice
    // /// ([`&[u8]`][byteslice]) is made of bytes, so this function converts between
    // /// the two. Not all byte slices are valid string slices, however: [`&str`] requires
    // /// that it is valid UTF-8. `from_utf8()` checks to ensure that the bytes are valid
    // /// UTF-8, and then does the conversion.
    // ///
    // /// [`&str`]: str
    // /// [byteslice]: slice
    // ///
    // /// If you are sure that the byte slice is valid UTF-8, and you don't want to
    // /// incur the overhead of the validity check, there is an unsafe version of
    // /// this function, [`from_utf8_unchecked`], which has the same
    // /// behavior but skips the check.
    // ///
    // /// If you need a `String` instead of a `&str`, consider
    // /// [`String::from_utf8`][string].
    // ///
    // /// [string]: ../../std/string/struct.String.html#method.from_utf8
    // ///
    // /// Because you can stack-allocate a `[u8; N]`, and you can take a
    // /// [`&[u8]`][byteslice] of it, this function is one way to have a
    // /// stack-allocated string. There is an example of this in the
    // /// examples section below.
    // ///
    // /// [byteslice]: slice
    // ///
    // /// # Errors
    // ///
    // /// Returns `Err` if the slice is not UTF-8 with a description as to why the
    // /// provided slice is not UTF-8.
    // ///
    // /// # Examples
    // ///
    // /// Basic usage:
    // ///
    // /// ```
    // /// use std::str;
    // ///
    // /// // some bytes, in a vector
    // /// let sparkle_heart = vec![240, 159, 146, 150];
    // ///
    // /// // We know these bytes are valid, so just use `unwrap()`.
    // /// let sparkle_heart = str::from_utf8(&sparkle_heart).unwrap();
    // ///
    // /// assert_eq!("💖", sparkle_heart);
    // /// ```
    // ///
    // /// Incorrect bytes:
    // ///
    // /// ```
    // /// use std::str;
    // ///
    // /// // some invalid bytes, in a vector
    // /// let sparkle_heart = vec![0, 159, 146, 150];
    // ///
    // /// assert!(str::from_utf8(&sparkle_heart).is_err());
    // /// ```
    // ///
    // /// See the docs for [`Utf8Error`] for more details on the kinds of
    // /// errors that can be returned.
    // ///
    // /// A "stack allocated string":
    // ///
    // /// ```
    // /// use std::str;
    // ///
    // /// // some bytes, in a stack-allocated array
    // /// let sparkle_heart = [240, 159, 146, 150];
    // ///
    // /// // We know these bytes are valid, so just use `unwrap()`.
    // /// let sparkle_heart = str::from_utf8(&sparkle_heart).unwrap();
    // ///
    // /// assert_eq!("💖", sparkle_heart);
    // /// ```
    // pub const fn from_utf8(v: &[u8]) -> Result<&str, Utf8Error> {
    //     // This should use `?` again, once it's `const`
    //     match run_utf8_validation(v) {
    //         Ok(_) => {
    //             // SAFETY: validation succeeded.
    //             Ok(unsafe { from_utf8_unchecked(v) })
    //         }
    //         Err(err) => Err(err),
    //     }
    // }

    // /// Converts a mutable slice of bytes to a mutable string slice.
    // ///
    // /// # Examples
    // ///
    // /// Basic usage:
    // ///
    // /// ```
    // /// use std::str;
    // ///
    // /// // "Hello, Rust!" as a mutable vector
    // /// let mut hellorust = vec![72, 101, 108, 108, 111, 44, 32, 82, 117, 115, 116, 33];
    // ///
    // /// // As we know these bytes are valid, we can use `unwrap()`
    // /// let outstr = str::from_utf8_mut(&mut hellorust).unwrap();
    // ///
    // /// assert_eq!("Hello, Rust!", outstr);
    // /// ```
    // ///
    // /// Incorrect bytes:
    // ///
    // /// ```
    // /// use std::str;
    // ///
    // /// // Some invalid bytes in a mutable vector
    // /// let mut invalid = vec![128, 223];
    // ///
    // /// assert!(str::from_utf8_mut(&mut invalid).is_err());
    // /// ```
    // /// See the docs for [`Utf8Error`] for more details on the kinds of
    // /// errors that can be returned.
    // pub const fn from_utf8_mut(v: &mut [u8]) -> Result<&mut str, Utf8Error> {
    //     // This should use `?` again, once it's `const`
    //     match run_utf8_validation(v) {
    //         Ok(_) => {
    //             // SAFETY: validation succeeded.
    //             Ok(unsafe { from_utf8_unchecked_mut(v) })
    //         }
    //         Err(err) => Err(err),
    //     }
    // }

    /// Converts a slice of bytes to a string slice without checking
    /// that the string contains valid UTF-8.
    ///
    /// See the safe version, [`from_utf8`], for more information.
    ///
    /// # Safety
    ///
    /// The bytes passed in must be valid UTF-8.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::str;
    ///
    /// // some bytes, in a vector
    /// let sparkle_heart = vec![240, 159, 146, 150];
    ///
    /// let sparkle_heart = unsafe {
    ///     str::from_utf8_unchecked(&sparkle_heart)
    /// };
    ///
    /// assert_eq!("💖", sparkle_heart);
    /// ```
    #[inline]
    #[must_use]
    pub const unsafe fn from_char_unchecked(v: &[char]) -> &u32str {
        // SAFETY: the caller must guarantee that the bytes `v` are valid UTF-8.
        // Also relies on `&u32str` and `&[char]` having the same layout.
        unsafe { mem::transmute(v) }
    }

    /// Converts a slice of bytes to a string slice without checking
    /// that the string contains valid UTF-8; mutable version.
    ///
    /// See the immutable version, [`from_utf8_unchecked()`] for more information.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::str;
    ///
    /// let mut heart = vec![240, 159, 146, 150];
    /// let heart = unsafe { str::from_utf8_unchecked_mut(&mut heart) };
    ///
    /// assert_eq!("💖", heart);
    /// ```
    #[inline]
    #[must_use]
    pub const unsafe fn from_char_unchecked_mut(v: &mut [char]) -> &mut u32str {
        // SAFETY: the caller must guarantee that the bytes `v`
        // are valid UTF-8, thus the cast to `*mut str` is safe.
        // Also, the pointer dereference is safe because that pointer
        // comes from a reference which is guaranteed to be valid for writes.
        unsafe { &mut *(v as *mut [char] as *mut u32str) }
    }

    // /// Converts a slice of bytes to a string slice without checking
    // /// that the string contains valid UTF-8.
    // ///
    // /// See the safe version, [`from_utf8`], for more information.
    // ///
    // /// # Safety
    // ///
    // /// The bytes passed in must be valid UTF-8.
    // ///
    // /// # Examples
    // ///
    // /// Basic usage:
    // ///
    // /// ```
    // /// use std::str;
    // ///
    // /// // some bytes, in a vector
    // /// let sparkle_heart = vec![240, 159, 146, 150];
    // ///
    // /// let sparkle_heart = unsafe {
    // ///     str::from_utf8_unchecked(&sparkle_heart)
    // /// };
    // ///
    // /// assert_eq!("💖", sparkle_heart);
    // /// ```
    // #[inline]
    // #[must_use]
    // pub const unsafe fn from_utf8_unchecked(v: &[u8]) -> &str {
    //     // SAFETY: the caller must guarantee that the bytes `v` are valid UTF-8.
    //     // Also relies on `&str` and `&[u8]` having the same layout.
    //     unsafe { mem::transmute(v) }
    // }

    // /// Converts a slice of bytes to a string slice without checking
    // /// that the string contains valid UTF-8; mutable version.
    // ///
    // /// See the immutable version, [`from_utf8_unchecked()`] for more information.
    // ///
    // /// # Examples
    // ///
    // /// Basic usage:
    // ///
    // /// ```
    // /// use std::str;
    // ///
    // /// let mut heart = vec![240, 159, 146, 150];
    // /// let heart = unsafe { str::from_utf8_unchecked_mut(&mut heart) };
    // ///
    // /// assert_eq!("💖", heart);
    // /// ```
    // #[inline]
    // #[must_use]
    // pub const unsafe fn from_utf8_unchecked_mut(v: &mut [u8]) -> &mut str {
    //     // SAFETY: the caller must guarantee that the bytes `v`
    //     // are valid UTF-8, thus the cast to `*mut str` is safe.
    //     // Also, the pointer dereference is safe because that pointer
    //     // comes from a reference which is guaranteed to be valid for writes.
    //     unsafe { &mut *(v as *mut [u8] as *mut str) }
    // }
}

/// Converts a boxed slice of bytes to a boxed string slice without checking
/// that the string contains valid UTF-8.
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// let smile_utf8 = Box::new([226, 152, 186]);
/// let smile = unsafe { std::str::from_boxed_utf8_unchecked(smile_utf8) };
///
/// assert_eq!("☺", &*smile);
/// ```
#[must_use]
#[inline]
pub unsafe fn from_boxed_utf8_unchecked(v: Box<[u8]>) -> Box<str> {
    unsafe { Box::from_raw(Box::into_raw(v) as *mut str) }
}

/// Converts the bytes while the bytes are still ascii.
/// For better average performance, this is happens in chunks of `2*size_of::<usize>()`.
/// Returns a vec with the converted bytes.
#[inline]
#[cfg(not(test))]
#[cfg(not(no_global_oom_handling))]
fn convert_while_ascii(b: &[u8], convert: fn(&u8) -> u8) -> Vec<u8> {
    let mut out = Vec::with_capacity(b.len());

    const USIZE_SIZE: usize = mem::size_of::<usize>();
    const MAGIC_UNROLL: usize = 2;
    const N: usize = USIZE_SIZE * MAGIC_UNROLL;
    const NONASCII_MASK: usize = usize::from_ne_bytes([0x80; USIZE_SIZE]);

    let mut i = 0;
    unsafe {
        while i + N <= b.len() {
            // Safety: we have checks the sizes `b` and `out` to know that our
            let in_chunk = b.get_unchecked(i..i + N);
            let out_chunk = out.spare_capacity_mut().get_unchecked_mut(i..i + N);

            let mut bits = 0;
            for j in 0..MAGIC_UNROLL {
                // read the bytes 1 usize at a time (unaligned since we haven't checked the alignment)
                // safety: in_chunk is valid bytes in the range
                bits |= in_chunk.as_ptr().cast::<usize>().add(j).read_unaligned();
            }
            // if our chunks aren't ascii, then return only the prior bytes as init
            if bits & NONASCII_MASK != 0 {
                break;
            }

            // perform the case conversions on N bytes (gets heavily autovec'd)
            for j in 0..N {
                // safety: in_chunk and out_chunk is valid bytes in the range
                let out = out_chunk.get_unchecked_mut(j);
                out.write(convert(in_chunk.get_unchecked(j)));
            }

            // mark these bytes as initialised
            i += N;
        }
        out.set_len(i);
    }

    out
}
