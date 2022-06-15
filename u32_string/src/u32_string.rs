//! A UTF-32–encoded, growable string.
//!
//! This module contains the [`U32String`] type, the [`ToU32String`] trait for
//! converting to strings, and several error types that may result from
//! working with [`U32String`]s.
//!
//! # Examples
//!
//! There are multiple ways to create a new [`U32String`] from a string literal:
//!
//! ```
//! let s = "Hello".to_string();
//!
//! let s = U32String::from("world");
//! let s: U32String = "also this".into();
//! ```
//!
//! You can create a new [`U32String`] from an existing one by concatenating with
//! `+`:
//!
//! ```
//! let s = "Hello".to_string();
//!
//! let message = s + " world!";
//! ```
//!
//! If you have a vector of valid UTF-8 bytes, you can make a [`U32String`] out of
//! it. You can do the reverse too.
//!
//! ```
//! let sparkle_heart = vec![240, 159, 146, 150];
//!
//! // We know these bytes are valid, so we'll use `unwrap()`.
//! let sparkle_heart = U32String::from_utf8(sparkle_heart).unwrap();
//!
//! assert_eq!("💖", sparkle_heart);
//!
//! let bytes = sparkle_heart.into_bytes();
//!
//! assert_eq!(bytes, [240, 159, 146, 150]);
//! ```

#[cfg(not(no_global_oom_handling))]
use core::char::{decode_utf16, REPLACEMENT_CHARACTER};
use core::fmt;
use core::hash;
#[cfg(not(no_global_oom_handling))]
use core::iter::FromIterator;
use core::iter::{from_fn, FusedIterator};
#[cfg(not(no_global_oom_handling))]
use core::ops::Add;
#[cfg(not(no_global_oom_handling))]
use core::ops::AddAssign;
#[cfg(not(no_global_oom_handling))]
use core::ops::Bound::{Excluded, Included, Unbounded};
use core::ops::{self, Range, RangeBounds};
use core::ptr;
use core::slice;
#[cfg(not(no_global_oom_handling))]
use core::str::lossy;
use core::str::pattern::Pattern;

use crate::u32str::u32str;
#[cfg(not(no_global_oom_handling))]
use std::borrow::{Cow, ToOwned};
use std::boxed::Box;
use std::collections::TryReserveError;
use std::str::{self, Chars, Utf8Error};
#[cfg(not(no_global_oom_handling))]
use std::str::{from_boxed_utf8_unchecked, FromStr};
use std::vec::Vec;

/// A UTF-8–encoded, growable string.
///
/// The `U32String` type is the most common string type that has ownership over the
/// contents of the string. It has a close relationship with its borrowed
/// counterpart, the primitive [`str`].
///
/// # Examples
///
/// You can create a `U32String` from [a literal string][`&str`] with [`U32String::from`]:
///
/// [`U32String::from`]: From::from
///
/// ```
/// let hello = U32String::from("Hello, world!");
/// ```
///
/// You can append a [`char`] to a `U32String` with the [`push`] method, and
/// append a [`&str`] with the [`push_str`] method:
///
/// ```
/// let mut hello = U32String::from("Hello, ");
///
/// hello.push('w');
/// hello.push_str("orld!");
/// ```
///
/// [`push`]: U32String::push
/// [`push_str`]: U32String::push_str
///
/// If you have a vector of UTF-8 bytes, you can create a `U32String` from it with
/// the [`from_utf8`] method:
///
/// ```
/// // some bytes, in a vector
/// let sparkle_heart = vec![240, 159, 146, 150];
///
/// // We know these bytes are valid, so we'll use `unwrap()`.
/// let sparkle_heart = U32String::from_utf8(sparkle_heart).unwrap();
///
/// assert_eq!("💖", sparkle_heart);
/// ```
///
/// [`from_utf8`]: U32String::from_utf8
///
/// # UTF-8
///
/// `U32String`s are always valid UTF-8. This has a few implications, the first of
/// which is that if you need a non-UTF-8 string, consider [`OsU32String`]. It is
/// similar, but without the UTF-8 constraint. The second implication is that
/// you cannot index into a `U32String`:
///
/// ```compile_fail,E0277
/// let s = "hello";
///
/// println!("The first letter of s is {}", s[0]); // ERROR!!!
/// ```
///
/// [`OsU32String`]: ../../std/ffi/struct.OsU32String.html "ffi::OsU32String"
///
/// Indexing is intended to be a constant-time operation, but UTF-8 encoding
/// does not allow us to do this. Furthermore, it's not clear what sort of
/// thing the index should return: a byte, a codepoint, or a grapheme cluster.
/// The [`bytes`] and [`chars`] methods return iterators over the first
/// two, respectively.
///
/// [`bytes`]: str::bytes
/// [`chars`]: str::chars
///
/// # Deref
///
/// `U32String` implements <code>[Deref]<Target = [str]></code>, and so inherits all of [`str`]'s
/// methods. In addition, this means that you can pass a `U32String` to a
/// function which takes a [`&str`] by using an ampersand (`&`):
///
/// ```
/// fn takes_str(s: &str) { }
///
/// let s = U32String::from("Hello");
///
/// takes_str(&s);
/// ```
///
/// This will create a [`&str`] from the `U32String` and pass it in. This
/// conversion is very inexpensive, and so generally, functions will accept
/// [`&str`]s as arguments unless they need a `U32String` for some specific
/// reason.
///
/// In certain cases Rust doesn't have enough information to make this
/// conversion, known as [`Deref`] coercion. In the following example a string
/// slice [`&'a str`][`&str`] implements the trait `TraitExample`, and the function
/// `example_func` takes anything that implements the trait. In this case Rust
/// would need to make two implicit conversions, which Rust doesn't have the
/// means to do. For that reason, the following example will not compile.
///
/// ```compile_fail,E0277
/// trait TraitExample {}
///
/// impl<'a> TraitExample for &'a str {}
///
/// fn example_func<A: TraitExample>(example_arg: A) {}
///
/// let example_string = U32String::from("example_string");
/// example_func(&example_string);
/// ```
///
/// There are two options that would work instead. The first would be to
/// change the line `example_func(&example_string);` to
/// `example_func(example_string.as_str());`, using the method [`as_str()`]
/// to explicitly extract the string slice containing the string. The second
/// way changes `example_func(&example_string);` to
/// `example_func(&*example_string);`. In this case we are dereferencing a
/// `U32String` to a [`str`], then referencing the [`str`] back to
/// [`&str`]. The second way is more idiomatic, however both work to do the
/// conversion explicitly rather than relying on the implicit conversion.
///
/// # Representation
///
/// A `U32String` is made up of three components: a pointer to some bytes, a
/// length, and a capacity. The pointer points to an internal buffer `U32String`
/// uses to store its data. The length is the number of bytes currently stored
/// in the buffer, and the capacity is the size of the buffer in bytes. As such,
/// the length will always be less than or equal to the capacity.
///
/// This buffer is always stored on the heap.
///
/// You can look at these with the [`as_ptr`], [`len`], and [`capacity`]
/// methods:
///
/// ```
/// use std::mem;
///
/// let story = U32String::from("Once upon a time...");
///
// FIXME Update this when vec_into_raw_parts is stabilized
/// // Prevent automatically dropping the U32String's data
/// let mut story = mem::ManuallyDrop::new(story);
///
/// let ptr = story.as_mut_ptr();
/// let len = story.len();
/// let capacity = story.capacity();
///
/// // story has nineteen bytes
/// assert_eq!(19, len);
///
/// // We can re-build a U32String out of ptr, len, and capacity. This is all
/// // unsafe because we are responsible for making sure the components are
/// // valid:
/// let s = unsafe { U32String::from_raw_parts(ptr, len, capacity) } ;
///
/// assert_eq!(U32String::from("Once upon a time..."), s);
/// ```
///
/// [`as_ptr`]: str::as_ptr
/// [`len`]: U32String::len
/// [`capacity`]: U32String::capacity
///
/// If a `U32String` has enough capacity, adding elements to it will not
/// re-allocate. For example, consider this program:
///
/// ```
/// let mut s = U32String::new();
///
/// println!("{}", s.capacity());
///
/// for _ in 0..5 {
///     s.push_str("hello");
///     println!("{}", s.capacity());
/// }
/// ```
///
/// This will output the following:
///
/// ```text
/// 0
/// 5
/// 10
/// 20
/// 20
/// 40
/// ```
///
/// At first, we have no memory allocated at all, but as we append to the
/// string, it increases its capacity appropriately. If we instead use the
/// [`with_capacity`] method to allocate the correct capacity initially:
///
/// ```
/// let mut s = U32String::with_capacity(25);
///
/// println!("{}", s.capacity());
///
/// for _ in 0..5 {
///     s.push_str("hello");
///     println!("{}", s.capacity());
/// }
/// ```
///
/// [`with_capacity`]: U32String::with_capacity
///
/// We end up with a different output:
///
/// ```text
/// 25
/// 25
/// 25
/// 25
/// 25
/// 25
/// ```
///
/// Here, there's no need to allocate more memory inside the loop.
///
/// [str]: prim@str "str"
/// [`str`]: prim@str "str"
/// [`&str`]: prim@str "&str"
/// [Deref]: core::ops::Deref "ops::Deref"
/// [`Deref`]: core::ops::Deref "ops::Deref"
/// [`as_str()`]: U32String::as_str
#[derive(PartialOrd, Eq, Ord)]
#[cfg_attr(not(test), rustc_diagnostic_item = "U32String")]
pub struct U32String {
    pub(crate) vec: Vec<char>,
}

/// A possible error value when converting a `U32String` from a UTF-8 byte vector.
///
/// This type is the error type for the [`from_utf8`] method on [`U32String`]. It
/// is designed in such a way to carefully avoid reallocations: the
/// [`into_bytes`] method will give back the byte vector that was used in the
/// conversion attempt.
///
/// [`from_utf8`]: U32String::from_utf8
/// [`into_bytes`]: FromUtf8Error::into_bytes
///
/// The [`Utf8Error`] type provided by [`std::str`] represents an error that may
/// occur when converting a slice of [`u8`]s to a [`&str`]. In this sense, it's
/// an analogue to `FromUtf8Error`, and you can get one from a `FromUtf8Error`
/// through the [`utf8_error`] method.
///
/// [`Utf8Error`]: str::Utf8Error "std::str::Utf8Error"
/// [`std::str`]: core::str "std::str"
/// [`&str`]: prim@str "&str"
/// [`utf8_error`]: FromUtf8Error::utf8_error
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// // some invalid bytes, in a vector
/// let bytes = vec![0, 159];
///
/// let value = U32String::from_utf8(bytes);
///
/// assert!(value.is_err());
/// assert_eq!(vec![0, 159], value.unwrap_err().into_bytes());
/// ```
#[cfg_attr(not(no_global_oom_handling), derive(Clone))]
#[derive(Debug, PartialEq, Eq)]
pub struct FromUtf8Error {
    bytes: Vec<u8>,
    error: Utf8Error,
}

/// A possible error value when converting a `U32String` from a UTF-16 byte slice.
///
/// This type is the error type for the [`from_utf16`] method on [`U32String`].
///
/// [`from_utf16`]: U32String::from_utf16
/// # Examples
///
/// Basic usage:
///
/// ```
/// // 𝄞mu<invalid>ic
/// let v = &[0xD834, 0xDD1E, 0x006d, 0x0075,
///           0xD800, 0x0069, 0x0063];
///
/// assert!(U32String::from_utf16(v).is_err());
/// ```
#[derive(Debug)]
pub struct FromUtf16Error(());

impl U32String {
    /// Creates a new empty `U32String`.
    ///
    /// Given that the `U32String` is empty, this will not allocate any initial
    /// buffer. While that means that this initial operation is very
    /// inexpensive, it may cause excessive allocation later when you add
    /// data. If you have an idea of how much data the `U32String` will hold,
    /// consider the [`with_capacity`] method to prevent excessive
    /// re-allocation.
    ///
    /// [`with_capacity`]: U32String::with_capacity
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let s = U32String::new();
    /// ```
    #[inline]
    #[must_use]
    pub const fn new() -> U32String {
        U32String { vec: Vec::new() }
    }

    /// Creates a new empty `U32String` with a particular capacity.
    ///
    /// `U32String`s have an internal buffer to hold their data. The capacity is
    /// the length of that buffer, and can be queried with the [`capacity`]
    /// method. This method creates an empty `U32String`, but one with an initial
    /// buffer that can hold `capacity` bytes. This is useful when you may be
    /// appending a bunch of data to the `U32String`, reducing the number of
    /// reallocations it needs to do.
    ///
    /// [`capacity`]: U32String::capacity
    ///
    /// If the given capacity is `0`, no allocation will occur, and this method
    /// is identical to the [`new`] method.
    ///
    /// [`new`]: U32String::new
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = U32String::with_capacity(10);
    ///
    /// // The U32String contains no chars, even though it has capacity for more
    /// assert_eq!(s.len(), 0);
    ///
    /// // These are all done without reallocating...
    /// let cap = s.capacity();
    /// for _ in 0..10 {
    ///     s.push('a');
    /// }
    ///
    /// assert_eq!(s.capacity(), cap);
    ///
    /// // ...but this may make the string reallocate
    /// s.push('a');
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    #[must_use]
    pub fn with_capacity(capacity: usize) -> U32String {
        U32String {
            vec: Vec::with_capacity(capacity),
        }
    }

    pub fn from_chars(chars: Vec<char>) -> U32String {
        U32String { vec: chars }
    }

    // HACK(japaric): with cfg(test) the inherent `[T]::to_vec` method, which is
    // required for this method definition, is not available. Since we don't
    // require this method for testing purposes, I'll just stub it
    // NB see the slice::hack module in slice.rs for more information
    #[inline]
    #[cfg(test)]
    pub fn from_str(_: &str) -> U32String {
        panic!("not available with cfg(test)");
    }

    /// Converts a vector of bytes to a `U32String`.
    ///
    /// A string ([`U32String`]) is made of bytes ([`u8`]), and a vector of bytes
    /// ([`Vec<u8>`]) is made of bytes, so this function converts between the
    /// two. Not all byte slices are valid `U32String`s, however: `U32String`
    /// requires that it is valid UTF-8. `from_utf8()` checks to ensure that
    /// the bytes are valid UTF-8, and then does the conversion.
    ///
    /// If you are sure that the byte slice is valid UTF-8, and you don't want
    /// to incur the overhead of the validity check, there is an unsafe version
    /// of this function, [`from_utf8_unchecked`], which has the same behavior
    /// but skips the check.
    ///
    /// This method will take care to not copy the vector, for efficiency's
    /// sake.
    ///
    /// If you need a [`&str`] instead of a `U32String`, consider
    /// [`str::from_utf8`].
    ///
    /// The inverse of this method is [`into_bytes`].
    ///
    /// # Errors
    ///
    /// Returns [`Err`] if the slice is not UTF-8 with a description as to why the
    /// provided bytes are not UTF-8. The vector you moved in is also included.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// // some bytes, in a vector
    /// let sparkle_heart = vec![240, 159, 146, 150];
    ///
    /// // We know these bytes are valid, so we'll use `unwrap()`.
    /// let sparkle_heart = U32String::from_utf8(sparkle_heart).unwrap();
    ///
    /// assert_eq!("💖", sparkle_heart);
    /// ```
    ///
    /// Incorrect bytes:
    ///
    /// ```
    /// // some invalid bytes, in a vector
    /// let sparkle_heart = vec![0, 159, 146, 150];
    ///
    /// assert!(U32String::from_utf8(sparkle_heart).is_err());
    /// ```
    ///
    /// See the docs for [`FromUtf8Error`] for more details on what you can do
    /// with this error.
    ///
    /// [`from_utf8_unchecked`]: U32String::from_utf8_unchecked
    /// [`Vec<u8>`]: crate::vec::Vec "Vec"
    /// [`&str`]: prim@str "&str"
    /// [`into_bytes`]: U32String::into_bytes
    #[inline]
    pub fn from_utf8(vec: Vec<u8>) -> Result<U32String, FromUtf8Error> {
        // TODO: Improve performance of this
        // https://trello.com/c/DCIsf6DI/1-improve-the-performance-of-the-u32stringfromutf8
        match str::from_utf8(&vec) {
            Ok(v) => Ok(U32String {
                vec: v.chars().collect(),
            }),
            Err(e) => Err(FromUtf8Error {
                bytes: vec,
                error: e,
            }),
        }
    }

    // /// Converts a slice of bytes to a string, including invalid characters.
    // ///
    // /// U32Strings are made of bytes ([`u8`]), and a slice of bytes
    // /// ([`&[u8]`][byteslice]) is made of bytes, so this function converts
    // /// between the two. Not all byte slices are valid strings, however: strings
    // /// are required to be valid UTF-8. During this conversion,
    // /// `from_utf8_lossy()` will replace any invalid UTF-8 sequences with
    // /// [`U+FFFD REPLACEMENT CHARACTER`][U+FFFD], which looks like this: �
    // ///
    // /// [byteslice]: prim@slice
    // /// [U+FFFD]: core::char::REPLACEMENT_CHARACTER
    // ///
    // /// If you are sure that the byte slice is valid UTF-8, and you don't want
    // /// to incur the overhead of the conversion, there is an unsafe version
    // /// of this function, [`from_utf8_unchecked`], which has the same behavior
    // /// but skips the checks.
    // ///
    // /// [`from_utf8_unchecked`]: U32String::from_utf8_unchecked
    // ///
    // /// This function returns a [`Cow<'a, u32str>`]. If our byte slice is invalid
    // /// UTF-8, then we need to insert the replacement characters, which will
    // /// change the size of the string, and hence, require a `U32String`. But if
    // /// it's already valid UTF-8, we don't need a new allocation. This return
    // /// type allows us to handle both cases.
    // ///
    // /// [`Cow<'a, u32str>`]: crate::borrow::Cow "borrow::Cow"
    // ///
    // /// # Examples
    // ///
    // /// Basic usage:
    // ///
    // /// ```
    // /// // some bytes, in a vector
    // /// let sparkle_heart = vec![240, 159, 146, 150];
    // ///
    // /// let sparkle_heart = U32String::from_utf8_lossy(&sparkle_heart);
    // ///
    // /// assert_eq!("💖", sparkle_heart);
    // /// ```
    // ///
    // /// Incorrect bytes:
    // ///
    // /// ```
    // /// // some invalid bytes
    // /// let input = b"Hello \xF0\x90\x80World";
    // /// let output = U32String::from_utf8_lossy(input);
    // ///
    // /// assert_eq!("Hello �World", output);
    // /// ```
    // #[must_use]
    // #[cfg(not(no_global_oom_handling))]
    // pub fn from_utf8_lossy(v: &[u8]) -> Cow<'_, u32str> {
    //     let mut iter = lossy::Utf8Lossy::from_bytes(v).chunks();
    //
    //     let first_valid = if let Some(chunk) = iter.next() {
    //         let lossy::Utf8LossyChunk { valid, broken } = chunk;
    //         if broken.is_empty() {
    //             debug_assert_eq!(valid.len(), v.len());
    //             return Cow::Borrowed(valid);
    //         }
    //         valid
    //     } else {
    //         return Cow::Borrowed("");
    //     };
    //
    //     const REPLACEMENT: &str = "\u{FFFD}";
    //
    //     let mut res = U32String::with_capacity(v.len());
    //     res.push_str(first_valid);
    //     res.push_str(REPLACEMENT);
    //
    //     for lossy::Utf8LossyChunk { valid, broken } in iter {
    //         res.push_str(valid);
    //         if !broken.is_empty() {
    //             res.push_str(REPLACEMENT);
    //         }
    //     }
    //
    //     Cow::Owned(res)
    // }

    /// Decode a UTF-16–encoded vector `v` into a `U32String`, returning [`Err`]
    /// if `v` contains any invalid data.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// // 𝄞music
    /// let v = &[0xD834, 0xDD1E, 0x006d, 0x0075,
    ///           0x0073, 0x0069, 0x0063];
    /// assert_eq!(U32String::from("𝄞music"),
    ///            U32String::from_utf16(v).unwrap());
    ///
    /// // 𝄞mu<invalid>ic
    /// let v = &[0xD834, 0xDD1E, 0x006d, 0x0075,
    ///           0xD800, 0x0069, 0x0063];
    /// assert!(U32String::from_utf16(v).is_err());
    /// ```
    #[cfg(not(no_global_oom_handling))]
    pub fn from_utf16(v: &[u16]) -> Result<U32String, FromUtf16Error> {
        // This isn't done via collect::<Result<_, _>>() for performance reasons.
        // FIXME: the function can be simplified again when #48994 is closed.
        let mut ret = U32String::with_capacity(v.len());
        for c in decode_utf16(v.iter().cloned()) {
            if let Ok(c) = c {
                ret.push(c);
            } else {
                return Err(FromUtf16Error(()));
            }
        }
        Ok(ret)
    }

    /// Decode a UTF-16–encoded slice `v` into a `U32String`, replacing
    /// invalid data with [the replacement character (`U+FFFD`)][U+FFFD].
    ///
    /// Unlike [`from_utf8_lossy`] which returns a [`Cow<'a, u32str>`],
    /// `from_utf16_lossy` returns a `U32String` since the UTF-16 to UTF-8
    /// conversion requires a memory allocation.
    ///
    /// [`from_utf8_lossy`]: U32String::from_utf8_lossy
    /// [`Cow<'a, u32str>`]: crate::borrow::Cow "borrow::Cow"
    /// [U+FFFD]: core::char::REPLACEMENT_CHARACTER
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// // 𝄞mus<invalid>ic<invalid>
    /// let v = &[0xD834, 0xDD1E, 0x006d, 0x0075,
    ///           0x0073, 0xDD1E, 0x0069, 0x0063,
    ///           0xD834];
    ///
    /// assert_eq!(U32String::from("𝄞mus\u{FFFD}ic\u{FFFD}"),
    ///            U32String::from_utf16_lossy(v));
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[must_use]
    #[inline]
    pub fn from_utf16_lossy(v: &[u16]) -> U32String {
        decode_utf16(v.iter().cloned())
            .map(|r| r.unwrap_or(REPLACEMENT_CHARACTER))
            .collect()
    }

    /// Decomposes a `U32String` into its raw components.
    ///
    /// Returns the raw pointer to the underlying data, the length of
    /// the string (in bytes), and the allocated capacity of the data
    /// (in bytes). These are the same arguments in the same order as
    /// the arguments to [`from_raw_parts`].
    ///
    /// After calling this function, the caller is responsible for the
    /// memory previously managed by the `U32String`. The only way to do
    /// this is to convert the raw pointer, length, and capacity back
    /// into a `U32String` with the [`from_raw_parts`] function, allowing
    /// the destructor to perform the cleanup.
    ///
    /// [`from_raw_parts`]: U32String::from_raw_parts
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(vec_into_raw_parts)]
    /// let s = U32String::from("hello");
    ///
    /// let (ptr, len, cap) = s.into_raw_parts();
    ///
    /// let rebuilt = unsafe { U32String::from_raw_parts(ptr, len, cap) };
    /// assert_eq!(rebuilt, "hello");
    /// ```
    #[must_use = "`self` will be dropped if the result is not used"]
    pub fn into_raw_parts(self) -> (*mut char, usize, usize) {
        self.vec.into_raw_parts()
    }

    /// Creates a new `U32String` from a length, capacity, and pointer.
    ///
    /// # Safety
    ///
    /// This is highly unsafe, due to the number of invariants that aren't
    /// checked:
    ///
    /// * The memory at `buf` needs to have been previously allocated by the
    ///   same allocator the standard library uses, with a required alignment of exactly 1.
    /// * `length` needs to be less than or equal to `capacity`.
    /// * `capacity` needs to be the correct value.
    /// * The first `length` bytes at `buf` need to be valid UTF-8.
    ///
    /// Violating these may cause problems like corrupting the allocator's
    /// internal data structures.
    ///
    /// The ownership of `buf` is effectively transferred to the
    /// `U32String` which may then deallocate, reallocate or change the
    /// contents of memory pointed to by the pointer at will. Ensure
    /// that nothing else uses the pointer after calling this
    /// function.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::mem;
    ///
    /// unsafe {
    ///     let s = U32String::from("hello");
    ///
    // FIXME Update this when vec_into_raw_parts is stabilized
    ///     // Prevent automatically dropping the U32String's data
    ///     let mut s = mem::ManuallyDrop::new(s);
    ///
    ///     let ptr = s.as_mut_ptr();
    ///     let len = s.len();
    ///     let capacity = s.capacity();
    ///
    ///     let s = U32String::from_raw_parts(ptr, len, capacity);
    ///
    ///     assert_eq!(U32String::from("hello"), s);
    /// }
    /// ```
    #[inline]
    pub unsafe fn from_raw_parts(buf: *mut char, length: usize, capacity: usize) -> U32String {
        unsafe {
            U32String {
                vec: Vec::from_raw_parts(buf, length, capacity),
            }
        }
    }

    // /// Converts a vector of bytes to a `U32String` without checking that the
    // /// string contains valid UTF-8.
    // ///
    // /// See the safe version, [`from_utf8`], for more details.
    // ///
    // /// [`from_utf8`]: U32String::from_utf8
    // ///
    // /// # Safety
    // ///
    // /// This function is unsafe because it does not check that the bytes passed
    // /// to it are valid UTF-8. If this constraint is violated, it may cause
    // /// memory unsafety issues with future users of the `U32String`, as the rest of
    // /// the standard library assumes that `U32String`s are valid UTF-8.
    // ///
    // /// # Examples
    // ///
    // /// Basic usage:
    // ///
    // /// ```
    // /// // some bytes, in a vector
    // /// let sparkle_heart = vec![240, 159, 146, 150];
    // ///
    // /// let sparkle_heart = unsafe {
    // ///     U32String::from_utf8_unchecked(sparkle_heart)
    // /// };
    // ///
    // /// assert_eq!("💖", sparkle_heart);
    // /// ```
    // #[inline]
    // #[must_use]
    // pub unsafe fn from_utf8_unchecked(bytes: Vec<u8>) -> U32String {
    //     U32String { vec: bytes }
    // }

    // /// Converts a `U32String` into a byte vector.
    // ///
    // /// This consumes the `U32String`, so we do not need to copy its contents.
    // ///
    // /// # Examples
    // ///
    // /// Basic usage:
    // ///
    // /// ```
    // /// let s = U32String::from("hello");
    // /// let bytes = s.into_bytes();
    // ///
    // /// assert_eq!(&[104, 101, 108, 108, 111][..], &bytes[..]);
    // /// ```
    // #[inline]
    // #[must_use = "`self` will be dropped if the result is not used"]
    // pub fn into_bytes(self) -> Vec<u8> {
    //     self.vec
    // }

    /// Extracts a string slice containing the entire `U32String`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let s = U32String::from("foo");
    ///
    /// assert_eq!("foo", s.as_str());
    /// ```
    #[inline]
    #[must_use]
    pub fn as_u32str(&self) -> &u32str {
        self
    }

    // TODO: Add as_str()

    /// Converts a `U32String` into a mutable string slice.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = U32String::from("foobar");
    /// let s_mut_str = s.as_mut_str();
    ///
    /// s_mut_str.make_ascii_uppercase();
    ///
    /// assert_eq!("FOOBAR", s_mut_str);
    /// ```
    #[inline]
    #[must_use]
    pub fn as_mut_u32str(&mut self) -> &mut u32str {
        self
    }

    // TODO: Add as_mut_str()

    /// Appends a given string slice onto the end of this `U32String`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = U32String::from("foo");
    ///
    /// s.push_str("bar");
    ///
    /// assert_eq!("foobar", s);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    pub fn push_str(&mut self, string: &str) {
        // TODO: Speed this up...
        let chars = string.chars().collect::<Vec<char>>();
        self.vec.extend_from_slice(&chars)
    }

    /// Appends a given string slice onto the end of this `U32String`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = U32String::from("foo");
    ///
    /// s.push_str("bar");
    ///
    /// assert_eq!("foobar", s);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    pub fn push_u32str(&mut self, string: &u32str) {
        self.vec.extend_from_slice(&string.data)
    }

    /// Copies elements from `src` range to the end of the string.
    ///
    /// ## Panics
    ///
    /// Panics if the starting point or end point do not lie on a [`char`]
    /// boundary, or if they're out of bounds.
    ///
    /// ## Examples
    ///
    /// ```
    /// #![feature(string_extend_from_within)]
    /// let mut string = U32String::from("abcde");
    ///
    /// string.extend_from_within(2..);
    /// assert_eq!(string, "abcdecde");
    ///
    /// string.extend_from_within(..2);
    /// assert_eq!(string, "abcdecdeab");
    ///
    /// string.extend_from_within(4..8);
    /// assert_eq!(string, "abcdecdeabecde");
    /// ```
    #[cfg(not(no_global_oom_handling))]
    pub fn extend_from_within<R>(&mut self, src: R)
    where
        R: RangeBounds<usize>,
    {
        let src @ Range { start, end } = slice::range(src, ..self.len());

        // TODO: Do we need this?
        // assert!(self.is_char_boundary(start));
        // assert!(self.is_char_boundary(end));

        self.vec.extend_from_within(src);
    }

    /// Returns this `U32String`'s capacity, in bytes.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let s = U32String::with_capacity(10);
    ///
    /// assert!(s.capacity() >= 10);
    /// ```
    #[inline]
    #[must_use]
    pub fn capacity(&self) -> usize {
        self.vec.capacity()
    }

    /// Ensures that this `U32String`'s capacity is at least `additional` bytes
    /// larger than its length.
    ///
    /// The capacity may be increased by more than `additional` bytes if it
    /// chooses, to prevent frequent reallocations.
    ///
    /// If you do not want this "at least" behavior, see the [`reserve_exact`]
    /// method.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows [`usize`].
    ///
    /// [`reserve_exact`]: U32String::reserve_exact
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = U32String::new();
    ///
    /// s.reserve(10);
    ///
    /// assert!(s.capacity() >= 10);
    /// ```
    ///
    /// This might not actually increase the capacity:
    ///
    /// ```
    /// let mut s = U32String::with_capacity(10);
    /// s.push('a');
    /// s.push('b');
    ///
    /// // s now has a length of 2 and a capacity of 10
    /// assert_eq!(2, s.len());
    /// assert_eq!(10, s.capacity());
    ///
    /// // Since we already have an extra 8 capacity, calling this...
    /// s.reserve(8);
    ///
    /// // ... doesn't actually increase.
    /// assert_eq!(10, s.capacity());
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.vec.reserve(additional)
    }

    /// Ensures that this `U32String`'s capacity is `additional` bytes
    /// larger than its length.
    ///
    /// Consider using the [`reserve`] method unless you absolutely know
    /// better than the allocator.
    ///
    /// [`reserve`]: U32String::reserve
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows `usize`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = U32String::new();
    ///
    /// s.reserve_exact(10);
    ///
    /// assert!(s.capacity() >= 10);
    /// ```
    ///
    /// This might not actually increase the capacity:
    ///
    /// ```
    /// let mut s = U32String::with_capacity(10);
    /// s.push('a');
    /// s.push('b');
    ///
    /// // s now has a length of 2 and a capacity of 10
    /// assert_eq!(2, s.len());
    /// assert_eq!(10, s.capacity());
    ///
    /// // Since we already have an extra 8 capacity, calling this...
    /// s.reserve_exact(8);
    ///
    /// // ... doesn't actually increase.
    /// assert_eq!(10, s.capacity());
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    pub fn reserve_exact(&mut self, additional: usize) {
        self.vec.reserve_exact(additional)
    }

    /// Tries to reserve capacity for at least `additional` more elements to be inserted
    /// in the given `U32String`. The collection may reserve more space to avoid
    /// frequent reallocations. After calling `reserve`, capacity will be
    /// greater than or equal to `self.len() + additional`. Does nothing if
    /// capacity is already sufficient.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error
    /// is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::TryReserveError;
    ///
    /// fn process_data(data: &str) -> Result<U32String, TryReserveError> {
    ///     let mut output = U32String::new();
    ///
    ///     // Pre-reserve the memory, exiting if we can't
    ///     output.try_reserve(data.len())?;
    ///
    ///     // Now we know this can't OOM in the middle of our complex work
    ///     output.push_str(data);
    ///
    ///     Ok(output)
    /// }
    /// # process_data("rust").expect("why is the test harness OOMing on 4 bytes?");
    /// ```
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.vec.try_reserve(additional)
    }

    /// Tries to reserve the minimum capacity for exactly `additional` more elements to
    /// be inserted in the given `U32String`. After calling `try_reserve_exact`,
    /// capacity will be greater than or equal to `self.len() + additional`.
    /// Does nothing if the capacity is already sufficient.
    ///
    /// Note that the allocator may give the collection more space than it
    /// requests. Therefore, capacity can not be relied upon to be precisely
    /// minimal. Prefer [`try_reserve`] if future insertions are expected.
    ///
    /// [`try_reserve`]: U32String::try_reserve
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error
    /// is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::collections::TryReserveError;
    ///
    /// fn process_data(data: &str) -> Result<U32String, TryReserveError> {
    ///     let mut output = U32String::new();
    ///
    ///     // Pre-reserve the memory, exiting if we can't
    ///     output.try_reserve_exact(data.len())?;
    ///
    ///     // Now we know this can't OOM in the middle of our complex work
    ///     output.push_str(data);
    ///
    ///     Ok(output)
    /// }
    /// # process_data("rust").expect("why is the test harness OOMing on 4 bytes?");
    /// ```
    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.vec.try_reserve_exact(additional)
    }

    /// Shrinks the capacity of this `U32String` to match its length.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = U32String::from("foo");
    ///
    /// s.reserve(100);
    /// assert!(s.capacity() >= 100);
    ///
    /// s.shrink_to_fit();
    /// assert_eq!(3, s.capacity());
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.vec.shrink_to_fit()
    }

    /// Shrinks the capacity of this `U32String` with a lower bound.
    ///
    /// The capacity will remain at least as large as both the length
    /// and the supplied value.
    ///
    /// If the current capacity is less than the lower limit, this is a no-op.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut s = U32String::from("foo");
    ///
    /// s.reserve(100);
    /// assert!(s.capacity() >= 100);
    ///
    /// s.shrink_to(10);
    /// assert!(s.capacity() >= 10);
    /// s.shrink_to(0);
    /// assert!(s.capacity() >= 3);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.vec.shrink_to(min_capacity)
    }

    /// Appends the given [`char`] to the end of this `U32String`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = U32String::from("abc");
    ///
    /// s.push('1');
    /// s.push('2');
    /// s.push('3');
    ///
    /// assert_eq!("abc123", s);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    pub fn push(&mut self, ch: char) {
        self.vec.push(ch)
    }

    // /// Returns a byte slice of this `U32String`'s contents.
    // ///
    // /// The inverse of this method is [`from_utf8`].
    // ///
    // /// [`from_utf8`]: U32String::from_utf8
    // ///
    // /// # Examples
    // ///
    // /// Basic usage:
    // ///
    // /// ```
    // /// let s = U32String::from("hello");
    // ///
    // /// assert_eq!(&[104, 101, 108, 108, 111], s.as_bytes());
    // /// ```
    // #[inline]
    // #[must_use]
    // pub fn as_bytes(&self) -> &[u8] {
    //     &self.vec
    // }

    /// Shortens this `U32String` to the specified length.
    ///
    /// If `new_len` is greater than the string's current length, this has no
    /// effect.
    ///
    /// Note that this method has no effect on the allocated capacity
    /// of the string
    ///
    /// # Panics
    ///
    /// Panics if `new_len` does not lie on a [`char`] boundary.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = U32String::from("hello");
    ///
    /// s.truncate(2);
    ///
    /// assert_eq!("he", s);
    /// ```
    #[inline]
    pub fn truncate(&mut self, new_len: usize) {
        if new_len <= self.len() {
            // TODO: Do we need this?
            // assert!(self.is_char_boundary(new_len));
            self.vec.truncate(new_len)
        }
    }

    /// Removes the last character from the string buffer and returns it.
    ///
    /// Returns [`None`] if this `U32String` is empty.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = U32String::from("foo");
    ///
    /// assert_eq!(s.pop(), Some('o'));
    /// assert_eq!(s.pop(), Some('o'));
    /// assert_eq!(s.pop(), Some('f'));
    ///
    /// assert_eq!(s.pop(), None);
    /// ```
    #[inline]
    pub fn pop(&mut self) -> Option<char> {
        self.vec.pop()
    }

    /// Removes a [`char`] from this `U32String` at a byte position and returns it.
    ///
    /// This is an *O*(*n*) operation, as it requires copying every element in the
    /// buffer.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than or equal to the `U32String`'s length,
    /// or if it does not lie on a [`char`] boundary.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = U32String::from("foo");
    ///
    /// assert_eq!(s.remove(0), 'f');
    /// assert_eq!(s.remove(1), 'o');
    /// assert_eq!(s.remove(0), 'o');
    /// ```
    #[inline]
    pub fn remove(&mut self, idx: usize) -> char {
        self.vec.remove(idx)
    }

    // /// Remove all matches of pattern `pat` in the `U32String`.
    // ///
    // /// # Examples
    // ///
    // /// ```
    // /// #![feature(string_remove_matches)]
    // /// let mut s = U32String::from("Trees are not green, the sky is not blue.");
    // /// s.remove_matches("not ");
    // /// assert_eq!("Trees are green, the sky is blue.", s);
    // /// ```
    // ///
    // /// Matches will be detected and removed iteratively, so in cases where
    // /// patterns overlap, only the first pattern will be removed:
    // ///
    // /// ```
    // /// #![feature(string_remove_matches)]
    // /// let mut s = U32String::from("banana");
    // /// s.remove_matches("ana");
    // /// assert_eq!("bna", s);
    // /// ```
    // #[cfg(not(no_global_oom_handling))]
    // pub fn remove_matches<'a, P>(&'a mut self, pat: P)
    // where
    //     P: for<'x> Pattern<'x>,
    // {
    //     use core::str::pattern::Searcher;
    //
    //     let rejections = {
    //         let mut searcher = pat.into_searcher(self);
    //         // Per Searcher::next:
    //         //
    //         // A Match result needs to contain the whole matched pattern,
    //         // however Reject results may be split up into arbitrary many
    //         // adjacent fragments. Both ranges may have zero length.
    //         //
    //         // In practice the implementation of Searcher::next_match tends to
    //         // be more efficient, so we use it here and do some work to invert
    //         // matches into rejections since that's what we want to copy below.
    //         let mut front = 0;
    //         let rejections: Vec<_> = from_fn(|| {
    //             let (start, end) = searcher.next_match()?;
    //             let prev_front = front;
    //             front = end;
    //             Some((prev_front, start))
    //         })
    //         .collect();
    //         rejections
    //             .into_iter()
    //             .chain(core::iter::once((front, self.len())))
    //     };
    //
    //     let mut len = 0;
    //     let ptr = self.vec.as_mut_ptr();
    //
    //     for (start, end) in rejections {
    //         let count = end - start;
    //         if start != len {
    //             // SAFETY: per Searcher::next:
    //             //
    //             // The stream of Match and Reject values up to a Done will
    //             // contain index ranges that are adjacent, non-overlapping,
    //             // covering the whole haystack, and laying on utf8
    //             // boundaries.
    //             unsafe {
    //                 ptr::copy(ptr.add(start), ptr.add(len), count);
    //             }
    //         }
    //         len += count;
    //     }
    //
    //     unsafe {
    //         self.vec.set_len(len);
    //     }
    // }

    // /// Retains only the characters specified by the predicate.
    // ///
    // /// In other words, remove all characters `c` such that `f(c)` returns `false`.
    // /// This method operates in place, visiting each character exactly once in the
    // /// original order, and preserves the order of the retained characters.
    // ///
    // /// # Examples
    // ///
    // /// ```
    // /// let mut s = U32String::from("f_o_ob_ar");
    // ///
    // /// s.retain(|c| c != '_');
    // ///
    // /// assert_eq!(s, "foobar");
    // /// ```
    // ///
    // /// Because the elements are visited exactly once in the original order,
    // /// external state may be used to decide which elements to keep.
    // ///
    // /// ```
    // /// let mut s = U32String::from("abcde");
    // /// let keep = [false, true, true, false, true];
    // /// let mut iter = keep.iter();
    // /// s.retain(|_| *iter.next().unwrap());
    // /// assert_eq!(s, "bce");
    // /// ```
    // #[inline]
    // pub fn retain<F>(&mut self, mut f: F)
    // where
    //     F: FnMut(char) -> bool,
    // {
    //     struct SetLenOnDrop<'a> {
    //         s: &'a mut U32String,
    //         idx: usize,
    //         del_bytes: usize,
    //     }
    //
    //     impl<'a> Drop for SetLenOnDrop<'a> {
    //         fn drop(&mut self) {
    //             let new_len = self.idx - self.del_bytes;
    //             debug_assert!(new_len <= self.s.len());
    //             unsafe { self.s.vec.set_len(new_len) };
    //         }
    //     }
    //
    //     let len = self.len();
    //     let mut guard = SetLenOnDrop {
    //         s: self,
    //         idx: 0,
    //         del_bytes: 0,
    //     };
    //
    //     while guard.idx < len {
    //         let ch = unsafe {
    //             guard
    //                 .s
    //                 .get_unchecked(guard.idx..len)
    //                 .chars()
    //                 .next()
    //                 .unwrap()
    //         };
    //         let ch_len = ch.len_utf8();
    //
    //         if !f(ch) {
    //             guard.del_bytes += ch_len;
    //         } else if guard.del_bytes > 0 {
    //             unsafe {
    //                 ptr::copy(
    //                     guard.s.vec.as_ptr().add(guard.idx),
    //                     guard.s.vec.as_mut_ptr().add(guard.idx - guard.del_bytes),
    //                     ch_len,
    //                 );
    //             }
    //         }
    //
    //         // Point idx to the next char
    //         guard.idx += ch_len;
    //     }
    //
    //     drop(guard);
    // }

    /// Inserts a character into this `U32String` at a byte position.
    ///
    /// This is an *O*(*n*) operation as it requires copying every element in the
    /// buffer.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than the `U32String`'s length, or if it does not
    /// lie on a [`char`] boundary.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = U32String::with_capacity(3);
    ///
    /// s.insert(0, 'f');
    /// s.insert(1, 'o');
    /// s.insert(2, 'o');
    ///
    /// assert_eq!("foo", s);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    pub fn insert(&mut self, idx: usize, ch: char) {
        // TODO: Do we need this?
        // assert!(self.is_char_boundary(idx));
        self.vec.insert(idx, ch)
        // let mut bits = [0; 4];
        // let bits = ch.encode_utf8(&mut bits).as_bytes();
        //
        // unsafe {
        //     self.insert_bytes(idx, bits);
        // }
    }

    // TODO: Implement insert_bytes
    // #[cfg(not(no_global_oom_handling))]
    // unsafe fn insert_bytes(&mut self, idx: usize, bytes: &[u8]) {
    //     let len = self.len();
    //     let amt = bytes.len();
    //     self.vec.reserve(amt);
    //
    //     unsafe {
    //         ptr::copy(
    //             self.vec.as_ptr().add(idx),
    //             self.vec.as_mut_ptr().add(idx + amt),
    //             len - idx,
    //         );
    //         ptr::copy_nonoverlapping(bytes.as_ptr(), self.vec.as_mut_ptr().add(idx), amt);
    //         self.vec.set_len(len + amt);
    //     }
    // }

    #[cfg(not(no_global_oom_handling))]
    unsafe fn insert_chars(&mut self, idx: usize, chars: &[char]) {
        let len = self.len();
        let amount = chars.len();
        self.vec.reserve(amount);
        unsafe {
            ptr::copy(
                self.vec.as_ptr().add(idx),
                self.vec.as_mut_ptr().add(idx + amount),
                len - idx,
            );
            ptr::copy_nonoverlapping(chars.as_ptr(), self.vec.as_mut_ptr().add(idx), amount);
            self.vec.set_len(len + amount);
        }
    }

    /// Inserts a string slice into this `U32String` at a byte position.
    ///
    /// This is an *O*(*n*) operation as it requires copying every element in the
    /// buffer.
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than the `U32String`'s length, or if it does not
    /// lie on a [`char`] boundary.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = U32String::from("bar");
    ///
    /// s.insert_str(0, "foo");
    ///
    /// assert_eq!("foobar", s);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    pub fn insert_u32str(&mut self, idx: usize, string: &u32str) {
        // TODO: Do we need this?
        // assert!(self.is_char_boundary(idx));
        unsafe {
            self.insert_chars(idx, &string.data);
        }
    }

    // TODO: Implement insert_str

    /// Returns a mutable reference to the contents of this `U32String`.
    ///
    /// # Safety
    ///
    /// This function is unsafe because the returned `&mut Vec` allows writing
    /// bytes which are not valid UTF-8. If this constraint is violated, using
    /// the original `U32String` after dropping the `&mut Vec` may violate memory
    /// safety, as the rest of the standard library assumes that `U32String`s are
    /// valid UTF-8.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = U32String::from("hello");
    ///
    /// unsafe {
    ///     let vec = s.as_mut_vec();
    ///     assert_eq!(&[104, 101, 108, 108, 111][..], &vec[..]);
    ///
    ///     vec.reverse();
    /// }
    /// assert_eq!(s, "olleh" );
    /// ```
    #[inline]
    pub unsafe fn as_mut_vec(&mut self) -> &mut Vec<char> {
        &mut self.vec
    }

    /// Returns the length of this `U32String`, in bytes, not [`char`]s or
    /// graphemes. In other words, it might not be what a human considers the
    /// length of the string.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let a = U32String::from("foo");
    /// assert_eq!(a.len(), 3);
    ///
    /// let fancy_f = U32String::from("ƒoo");
    /// assert_eq!(fancy_f.len(), 4);
    /// assert_eq!(fancy_f.chars().count(), 3);
    /// ```
    #[inline]
    #[must_use]
    pub fn len(&self) -> usize {
        self.vec.len()
    }

    /// Returns `true` if this `U32String` has a length of zero, and `false` otherwise.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut v = U32String::new();
    /// assert!(v.is_empty());
    ///
    /// v.push('a');
    /// assert!(!v.is_empty());
    /// ```
    #[inline]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Splits the string into two at the given byte index.
    ///
    /// Returns a newly allocated `U32String`. `self` contains bytes `[0, at)`, and
    /// the returned `U32String` contains bytes `[at, len)`. `at` must be on the
    /// boundary of a UTF-8 code point.
    ///
    /// Note that the capacity of `self` does not change.
    ///
    /// # Panics
    ///
    /// Panics if `at` is not on a `UTF-8` code point boundary, or if it is beyond the last
    /// code point of the string.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() {
    /// let mut hello = U32String::from("Hello, World!");
    /// let world = hello.split_off(7);
    /// assert_eq!(hello, "Hello, ");
    /// assert_eq!(world, "World!");
    /// # }
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    #[must_use = "use `.truncate()` if you don't need the other half"]
    pub fn split_off(&mut self, at: usize) -> U32String {
        // TODO: Do we need this?
        // assert!(self.is_char_boundary(at));
        let other = self.vec.split_off(at);
        // unsafe { U32String::from_utf8_unchecked(other) }
        U32String { vec: other }
    }

    /// Truncates this `U32String`, removing all contents.
    ///
    /// While this means the `U32String` will have a length of zero, it does not
    /// touch its capacity.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = U32String::from("foo");
    ///
    /// s.clear();
    ///
    /// assert!(s.is_empty());
    /// assert_eq!(0, s.len());
    /// assert_eq!(3, s.capacity());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.vec.clear()
    }

    // /// Removes the specified range from the string in bulk, returning all
    // /// removed characters as an iterator.
    // ///
    // /// The returned iterator keeps a mutable borrow on the string to optimize
    // /// its implementation.
    // ///
    // /// # Panics
    // ///
    // /// Panics if the starting point or end point do not lie on a [`char`]
    // /// boundary, or if they're out of bounds.
    // ///
    // /// # Leaking
    // ///
    // /// If the returned iterator goes out of scope without being dropped (due to
    // /// [`core::mem::forget`], for example), the string may still contain a copy
    // /// of any drained characters, or may have lost characters arbitrarily,
    // /// including characters outside the range.
    // ///
    // /// # Examples
    // ///
    // /// Basic usage:
    // ///
    // /// ```
    // /// let mut s = U32String::from("α is alpha, β is beta");
    // /// let beta_offset = s.find('β').unwrap_or(s.len());
    // ///
    // /// // Remove the range up until the β from the string
    // /// let t: U32String = s.drain(..beta_offset).collect();
    // /// assert_eq!(t, "α is alpha, ");
    // /// assert_eq!(s, "β is beta");
    // ///
    // /// // A full range clears the string, like `clear()` does
    // /// s.drain(..);
    // /// assert_eq!(s, "");
    // /// ```
    // pub fn drain<R>(&mut self, range: R) -> Drain<'_>
    // where
    //     R: RangeBounds<usize>,
    // {
    //     // Memory safety
    //     //
    //     // The U32String version of Drain does not have the memory safety issues
    //     // of the vector version. The data is just plain bytes.
    //     // Because the range removal happens in Drop, if the Drain iterator is leaked,
    //     // the removal will not happen.
    //     let Range { start, end } = slice::range(range, ..self.len());
    //     // TODO: Do we need this?
    //     // assert!(self.is_char_boundary(start));
    //     // assert!(self.is_char_boundary(end));
    //
    //     // Take out two simultaneous borrows. The &mut U32String won't be accessed
    //     // until iteration is over, in Drop.
    //     let self_ptr = self as *mut _;
    //     // SAFETY: `slice::range` and `is_char_boundary` do the appropriate bounds checks.
    //     let chars_iter = unsafe { self.get_unchecked(start..end) }.chars();
    //
    //     Drain {
    //         start,
    //         end,
    //         iter: chars_iter,
    //         string: self_ptr,
    //     }
    // }

    // /// Removes the specified range in the string,
    // /// and replaces it with the given string.
    // /// The given string doesn't need to be the same length as the range.
    // ///
    // /// # Panics
    // ///
    // /// Panics if the starting point or end point do not lie on a [`char`]
    // /// boundary, or if they're out of bounds.
    // ///
    // /// # Examples
    // ///
    // /// Basic usage:
    // ///
    // /// ```
    // /// let mut s = U32String::from("α is alpha, β is beta");
    // /// let beta_offset = s.find('β').unwrap_or(s.len());
    // ///
    // /// // Replace the range up until the β from the string
    // /// s.replace_range(..beta_offset, "Α is capital alpha; ");
    // /// assert_eq!(s, "Α is capital alpha; β is beta");
    // /// ```
    // #[cfg(not(no_global_oom_handling))]
    // pub fn replace_range<R>(&mut self, range: R, replace_with: &str)
    // where
    //     R: RangeBounds<usize>,
    // {
    //     // Memory safety
    //     //
    //     // Replace_range does not have the memory safety issues of a vector Splice.
    //     // of the vector version. The data is just plain bytes.
    //
    //     // WARNING: Inlining this variable would be unsound (#81138)
    //     let start = range.start_bound();
    //     // TODO: Do we need this?
    //     // match start {
    //     //     Included(&n) => assert!(self.is_char_boundary(n)),
    //     //     Excluded(&n) => assert!(self.is_char_boundary(n + 1)),
    //     //     Unbounded => {}
    //     // };
    //     // WARNING: Inlining this variable would be unsound (#81138)
    //     let end = range.end_bound();
    //     // TODO: Do we need this?
    //     // match end {
    //     //     Included(&n) => assert!(self.is_char_boundary(n + 1)),
    //     //     Excluded(&n) => assert!(self.is_char_boundary(n)),
    //     //     Unbounded => {}
    //     // };
    //
    //     // Using `range` again would be unsound (#81138)
    //     // We assume the bounds reported by `range` remain the same, but
    //     // an adversarial implementation could change between calls
    //     unsafe { self.as_mut_vec() }.splice((start, end), replace_with.bytes());
    // }

    /// Converts this `U32String` into a <code>[Box]<[str]></code>.
    ///
    /// This will drop any excess capacity.
    ///
    /// [str]: prim@str "str"
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let s = U32String::from("hello");
    ///
    /// let b = s.into_boxed_str();
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[must_use = "`self` will be dropped if the result is not used"]
    #[inline]
    pub fn into_boxed_u32str(self) -> Box<u32str> {
        let slice = self.vec.into_boxed_slice();
        unsafe { u32str::from_boxed_chars(slice) }
    }
}

impl FromUtf8Error {
    /// Returns a slice of [`u8`]s bytes that were attempted to convert to a `U32String`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// // some invalid bytes, in a vector
    /// let bytes = vec![0, 159];
    ///
    /// let value = U32String::from_utf8(bytes);
    ///
    /// assert_eq!(&[0, 159], value.unwrap_err().as_bytes());
    /// ```
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes[..]
    }

    /// Returns the bytes that were attempted to convert to a `U32String`.
    ///
    /// This method is carefully constructed to avoid allocation. It will
    /// consume the error, moving out the bytes, so that a copy of the bytes
    /// does not need to be made.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// // some invalid bytes, in a vector
    /// let bytes = vec![0, 159];
    ///
    /// let value = U32String::from_utf8(bytes);
    ///
    /// assert_eq!(vec![0, 159], value.unwrap_err().into_bytes());
    /// ```
    #[must_use = "`self` will be dropped if the result is not used"]
    pub fn into_bytes(self) -> Vec<u8> {
        self.bytes
    }

    /// Fetch a `Utf8Error` to get more details about the conversion failure.
    ///
    /// The [`Utf8Error`] type provided by [`std::str`] represents an error that may
    /// occur when converting a slice of [`u8`]s to a [`&str`]. In this sense, it's
    /// an analogue to `FromUtf8Error`. See its documentation for more details
    /// on using it.
    ///
    /// [`std::str`]: core::str "std::str"
    /// [`&str`]: prim@str "&str"
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// // some invalid bytes, in a vector
    /// let bytes = vec![0, 159];
    ///
    /// let error = U32String::from_utf8(bytes).unwrap_err().utf8_error();
    ///
    /// // the first byte is invalid here
    /// assert_eq!(1, error.valid_up_to());
    /// ```
    #[must_use]
    pub fn utf8_error(&self) -> Utf8Error {
        self.error
    }
}

impl fmt::Display for FromUtf8Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.error, f)
    }
}

impl fmt::Display for FromUtf16Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt("invalid utf-16: lone surrogate found", f)
    }
}

#[cfg(not(no_global_oom_handling))]
impl Clone for U32String {
    fn clone(&self) -> Self {
        U32String {
            vec: self.vec.clone(),
        }
    }

    fn clone_from(&mut self, source: &Self) {
        self.vec.clone_from(&source.vec);
    }
}

#[cfg(not(no_global_oom_handling))]
impl FromIterator<char> for U32String {
    fn from_iter<I: IntoIterator<Item = char>>(iter: I) -> U32String {
        let mut buf = U32String::new();
        buf.extend(iter);
        buf
    }
}

#[cfg(not(no_global_oom_handling))]
impl<'a> FromIterator<&'a char> for U32String {
    fn from_iter<I: IntoIterator<Item = &'a char>>(iter: I) -> U32String {
        let mut buf = U32String::new();
        buf.extend(iter);
        buf
    }
}

#[cfg(not(no_global_oom_handling))]
impl<'a> FromIterator<&'a u32str> for U32String {
    fn from_iter<I: IntoIterator<Item = &'a u32str>>(iter: I) -> U32String {
        let mut buf = U32String::new();
        buf.extend(iter);
        buf
    }
}

#[cfg(not(no_global_oom_handling))]
impl FromIterator<U32String> for U32String {
    fn from_iter<I: IntoIterator<Item = U32String>>(iter: I) -> U32String {
        let mut iterator = iter.into_iter();

        // Because we're iterating over `U32String`s, we can avoid at least
        // one allocation by getting the first string from the iterator
        // and appending to it all the subsequent strings.
        match iterator.next() {
            None => U32String::new(),
            Some(mut buf) => {
                buf.extend(iterator);
                buf
            }
        }
    }
}

#[cfg(not(no_global_oom_handling))]
impl FromIterator<Box<u32str>> for U32String {
    fn from_iter<I: IntoIterator<Item = Box<u32str>>>(iter: I) -> U32String {
        let mut buf = U32String::new();
        buf.extend(iter);
        buf
    }
}

#[cfg(not(no_global_oom_handling))]
impl<'a> FromIterator<Cow<'a, u32str>> for U32String {
    fn from_iter<I: IntoIterator<Item = Cow<'a, u32str>>>(iter: I) -> U32String {
        let mut iterator = iter.into_iter();

        // Because we're iterating over CoWs, we can (potentially) avoid at least
        // one allocation by getting the first item and appending to it all the
        // subsequent items.
        match iterator.next() {
            None => U32String::new(),
            Some(cow) => {
                let mut buf = cow.into_owned();
                buf.extend(iterator);
                buf
            }
        }
    }
}

#[cfg(not(no_global_oom_handling))]
impl Extend<char> for U32String {
    fn extend<I: IntoIterator<Item = char>>(&mut self, iter: I) {
        let iterator = iter.into_iter();
        let (lower_bound, _) = iterator.size_hint();
        self.reserve(lower_bound);
        iterator.for_each(move |c| self.push(c));
    }

    #[inline]
    fn extend_one(&mut self, c: char) {
        self.push(c);
    }

    #[inline]
    fn extend_reserve(&mut self, additional: usize) {
        self.reserve(additional);
    }
}

#[cfg(not(no_global_oom_handling))]
impl<'a> Extend<&'a char> for U32String {
    fn extend<I: IntoIterator<Item = &'a char>>(&mut self, iter: I) {
        self.extend(iter.into_iter().cloned());
    }

    #[inline]
    fn extend_one(&mut self, &c: &'a char) {
        self.push(c);
    }

    #[inline]
    fn extend_reserve(&mut self, additional: usize) {
        self.reserve(additional);
    }
}

#[cfg(not(no_global_oom_handling))]
impl<'a> Extend<&'a u32str> for U32String {
    fn extend<I: IntoIterator<Item = &'a u32str>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |s| self.push_u32str(s));
    }

    #[inline]
    fn extend_one(&mut self, s: &'a u32str) {
        self.push_u32str(s);
    }
}

#[cfg(not(no_global_oom_handling))]
impl Extend<Box<u32str>> for U32String {
    fn extend<I: IntoIterator<Item = Box<u32str>>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |s| self.push_u32str(&s));
    }
}

#[cfg(not(no_global_oom_handling))]
impl Extend<U32String> for U32String {
    fn extend<I: IntoIterator<Item = U32String>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |s| self.push_u32str(&s));
    }

    #[inline]
    fn extend_one(&mut self, s: U32String) {
        self.push_u32str(&s);
    }
}

#[cfg(not(no_global_oom_handling))]
impl<'a> Extend<Cow<'a, u32str>> for U32String {
    fn extend<I: IntoIterator<Item = Cow<'a, u32str>>>(&mut self, iter: I) {
        iter.into_iter().for_each(move |s| self.push_u32str(&s));
    }

    #[inline]
    fn extend_one(&mut self, s: Cow<'a, u32str>) {
        self.push_u32str(&s);
    }
}

// /// A convenience impl that delegates to the impl for `&str`.
// ///
// /// # Examples
// ///
// /// ```
// /// assert_eq!(U32String::from("Hello world").find("world"), Some(6));
// /// ```
// impl<'a, 'b> Pattern<'a> for &'b U32String {
//     type Searcher = <&'b str as Pattern<'a>>::Searcher;
//
//     fn into_searcher(self, haystack: &'a str) -> <&'b str as Pattern<'a>>::Searcher {
//         self[..].into_searcher(haystack)
//     }
//
//     #[inline]
//     fn is_contained_in(self, haystack: &'a str) -> bool {
//         self[..].is_contained_in(haystack)
//     }
//
//     #[inline]
//     fn is_prefix_of(self, haystack: &'a str) -> bool {
//         self[..].is_prefix_of(haystack)
//     }
//
//     #[inline]
//     fn strip_prefix_of(self, haystack: &'a str) -> Option<&'a str> {
//         self[..].strip_prefix_of(haystack)
//     }
//
//     #[inline]
//     fn is_suffix_of(self, haystack: &'a str) -> bool {
//         self[..].is_suffix_of(haystack)
//     }
//
//     #[inline]
//     fn strip_suffix_of(self, haystack: &'a str) -> Option<&'a str> {
//         self[..].strip_suffix_of(haystack)
//     }
// }

impl PartialEq for U32String {
    #[inline]
    fn eq(&self, other: &U32String) -> bool {
        PartialEq::eq(&self[..], &other[..])
    }
    #[inline]
    fn ne(&self, other: &U32String) -> bool {
        PartialEq::ne(&self[..], &other[..])
    }
}

macro_rules! impl_eq {
    ($lhs:ty, $rhs: ty) => {
        #[allow(unused_lifetimes)]
        impl<'a, 'b> PartialEq<$rhs> for $lhs {
            #[inline]
            fn eq(&self, other: &$rhs) -> bool {
                PartialEq::eq(&self[..], &other[..])
            }
            #[inline]
            fn ne(&self, other: &$rhs) -> bool {
                PartialEq::ne(&self[..], &other[..])
            }
        }

        #[allow(unused_lifetimes)]
        impl<'a, 'b> PartialEq<$lhs> for $rhs {
            #[inline]
            fn eq(&self, other: &$lhs) -> bool {
                PartialEq::eq(&self[..], &other[..])
            }
            #[inline]
            fn ne(&self, other: &$lhs) -> bool {
                PartialEq::ne(&self[..], &other[..])
            }
        }
    };
}

impl_eq! { U32String, u32str }
impl_eq! { U32String, &'a u32str }
#[cfg(not(no_global_oom_handling))]
impl_eq! { Cow<'a, u32str>, u32str }
#[cfg(not(no_global_oom_handling))]
impl_eq! { Cow<'a, u32str>, &'b u32str }
#[cfg(not(no_global_oom_handling))]
impl_eq! { Cow<'a, u32str>, U32String }

impl const Default for U32String {
    /// Creates an empty `U32String`.
    #[inline]
    fn default() -> U32String {
        U32String::new()
    }
}

impl fmt::Display for U32String {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl fmt::Debug for U32String {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl hash::Hash for U32String {
    #[inline]
    fn hash<H: hash::Hasher>(&self, hasher: &mut H) {
        (**self).hash(hasher)
    }
}

/// Implements the `+` operator for concatenating two strings.
///
/// This consumes the `U32String` on the left-hand side and re-uses its buffer (growing it if
/// necessary). This is done to avoid allocating a new `U32String` and copying the entire contents on
/// every operation, which would lead to *O*(*n*^2) running time when building an *n*-byte string by
/// repeated concatenation.
///
/// The string on the right-hand side is only borrowed; its contents are copied into the returned
/// `U32String`.
///
/// # Examples
///
/// Concatenating two `U32String`s takes the first by value and borrows the second:
///
/// ```
/// let a = U32String::from("hello");
/// let b = U32String::from(" world");
/// let c = a + &b;
/// // `a` is moved and can no longer be used here.
/// ```
///
/// If you want to keep using the first `U32String`, you can clone it and append to the clone instead:
///
/// ```
/// let a = U32String::from("hello");
/// let b = U32String::from(" world");
/// let c = a.clone() + &b;
/// // `a` is still valid here.
/// ```
///
/// Concatenating `&str` slices can be done by converting the first to a `U32String`:
///
/// ```
/// let a = "hello";
/// let b = " world";
/// let c = a.to_string() + b;
/// ```
#[cfg(not(no_global_oom_handling))]
impl Add<&u32str> for U32String {
    type Output = U32String;

    #[inline]
    fn add(mut self, other: &u32str) -> U32String {
        self.push_u32str(other);
        self
    }
}

/// Implements the `+=` operator for appending to a `U32String`.
///
/// This has the same behavior as the [`push_str`][U32String::push_str] method.
#[cfg(not(no_global_oom_handling))]
impl AddAssign<&u32str> for U32String {
    #[inline]
    fn add_assign(&mut self, other: &u32str) {
        self.push_u32str(other);
    }
}

impl ops::Index<ops::Range<usize>> for U32String {
    type Output = u32str;

    #[inline]
    fn index(&self, index: ops::Range<usize>) -> &u32str {
        &self[..][index]
    }
}
impl ops::Index<ops::RangeTo<usize>> for U32String {
    type Output = u32str;

    #[inline]
    fn index(&self, index: ops::RangeTo<usize>) -> &u32str {
        &self[..][index]
    }
}
impl ops::Index<ops::RangeFrom<usize>> for U32String {
    type Output = u32str;

    #[inline]
    fn index(&self, index: ops::RangeFrom<usize>) -> &u32str {
        &self[..][index]
    }
}
impl ops::Index<ops::RangeFull> for U32String {
    type Output = u32str;

    #[inline]
    fn index(&self, _index: ops::RangeFull) -> &u32str {
        // unsafe { str::from_utf8_unchecked(&self.vec) }
        &self[..]
    }
}
impl ops::Index<ops::RangeInclusive<usize>> for U32String {
    type Output = u32str;

    #[inline]
    fn index(&self, index: ops::RangeInclusive<usize>) -> &u32str {
        ops::Index::index(&**self, index)
    }
}
impl ops::Index<ops::RangeToInclusive<usize>> for U32String {
    type Output = u32str;

    #[inline]
    fn index(&self, index: ops::RangeToInclusive<usize>) -> &u32str {
        ops::Index::index(&**self, index)
    }
}

impl ops::IndexMut<ops::Range<usize>> for U32String {
    #[inline]
    fn index_mut(&mut self, index: ops::Range<usize>) -> &mut u32str {
        &mut self[..][index]
    }
}
impl ops::IndexMut<ops::RangeTo<usize>> for U32String {
    #[inline]
    fn index_mut(&mut self, index: ops::RangeTo<usize>) -> &mut u32str {
        &mut self[..][index]
    }
}
impl ops::IndexMut<ops::RangeFrom<usize>> for U32String {
    #[inline]
    fn index_mut(&mut self, index: ops::RangeFrom<usize>) -> &mut u32str {
        &mut self[..][index]
    }
}
impl ops::IndexMut<ops::RangeFull> for U32String {
    #[inline]
    fn index_mut(&mut self, _index: ops::RangeFull) -> &mut u32str {
        // unsafe { str::from_utf8_unchecked_mut(&mut *self.vec) }
        &mut self
    }
}
impl ops::IndexMut<ops::RangeInclusive<usize>> for U32String {
    #[inline]
    fn index_mut(&mut self, index: ops::RangeInclusive<usize>) -> &mut u32str {
        ops::IndexMut::index_mut(&mut **self, index)
    }
}
impl ops::IndexMut<ops::RangeToInclusive<usize>> for U32String {
    #[inline]
    fn index_mut(&mut self, index: ops::RangeToInclusive<usize>) -> &mut u32str {
        ops::IndexMut::index_mut(&mut **self, index)
    }
}

impl ops::Deref for U32String {
    type Target = u32str;

    #[inline]
    fn deref(&self) -> &u32str {
        // unsafe { str::from_utf8_unchecked(&self.vec) }
        unsafe { u32str::from_char_unchecked(&self.vec) }
    }
}

impl ops::DerefMut for U32String {
    #[inline]
    fn deref_mut(&mut self) -> &mut u32str {
        // unsafe { str::from_utf8_unchecked_mut(&mut *self.vec) }
        unsafe { u32str::from_char_unchecked_mut(&mut *self.vec) }
    }
}

/// A type alias for [`Infallible`].
///
/// This alias exists for backwards compatibility, and may be eventually deprecated.
///
/// [`Infallible`]: core::convert::Infallible "convert::Infallible"
pub type ParseError = core::convert::Infallible;

// #[cfg(not(no_global_oom_handling))]
// impl FromStr for U32String {
//     type Err = core::convert::Infallible;
//     #[inline]
//     fn from_str(s: &str) -> Result<U32String, Self::Err> {
//         Ok(U32String::from(s))
//     }
// }

/// A trait for converting a value to a `U32String`.
///
/// This trait is automatically implemented for any type which implements the
/// [`Display`] trait. As such, `ToU32String` shouldn't be implemented directly:
/// [`Display`] should be implemented instead, and you get the `ToU32String`
/// implementation for free.
///
/// [`Display`]: fmt::Display
#[cfg_attr(not(test), rustc_diagnostic_item = "ToU32String")]
pub trait ToU32String {
    /// Converts the given value to a `U32String`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let i = 5;
    /// let five = U32String::from("5");
    ///
    /// assert_eq!(five, i.to_string());
    /// ```
    #[rustc_conversion_suggestion]
    fn to_string(&self) -> U32String;
}

/// # Panics
///
/// In this implementation, the `to_string` method panics
/// if the `Display` implementation returns an error.
/// This indicates an incorrect `Display` implementation
/// since `fmt::Write for U32String` never returns an error itself.
#[cfg(not(no_global_oom_handling))]
impl<T: fmt::Display + ?Sized> ToU32String for T {
    // A common guideline is to not inline generic functions. However,
    // removing `#[inline]` from this method causes non-negligible regressions.
    // See <https://github.com/rust-lang/rust/pull/74852>, the last attempt
    // to try to remove it.
    #[inline]
    default fn to_string(&self) -> U32String {
        let mut buf = U32String::new();
        let mut formatter = fmt::Formatter::new(&mut buf);
        // Bypass format_args!() to avoid write_str with zero-length strs
        fmt::Display::fmt(self, &mut formatter)
            .expect("a Display implementation returned an error unexpectedly");
        buf
    }
}

#[cfg(not(no_global_oom_handling))]
impl ToU32String for char {
    #[inline]
    fn to_string(&self) -> U32String {
        U32String::from(*self)
    }
}

#[cfg(not(no_global_oom_handling))]
impl ToU32String for u8 {
    #[inline]
    fn to_string(&self) -> U32String {
        let mut buf = U32String::with_capacity(3);
        let mut n = *self;
        if n >= 10 {
            if n >= 100 {
                buf.push((b'0' + n / 100) as char);
                n %= 100;
            }
            buf.push((b'0' + n / 10) as char);
            n %= 10;
        }
        buf.push((b'0' + n) as char);
        buf
    }
}

#[cfg(not(no_global_oom_handling))]
impl ToU32String for i8 {
    #[inline]
    fn to_string(&self) -> U32String {
        let mut buf = U32String::with_capacity(4);
        if self.is_negative() {
            buf.push('-');
        }
        let mut n = self.unsigned_abs();
        if n >= 10 {
            if n >= 100 {
                buf.push('1');
                n -= 100;
            }
            buf.push((b'0' + n / 10) as char);
            n %= 10;
        }
        buf.push((b'0' + n) as char);
        buf
    }
}

#[cfg(not(no_global_oom_handling))]
impl ToU32String for u32str {
    #[inline]
    fn to_string(&self) -> U32String {
        U32String::from(self)
    }
}

// TODO: This conflicts with impl<T: fmt::Display + ?Sized> ToU32String for T {
// #[cfg(not(no_global_oom_handling))]
// impl ToU32String for Cow<'_, u32str> {
//     #[inline]
//     fn to_string(&self) -> U32String {
//         self[..].to_owned()
//     }
// }

#[cfg(not(no_global_oom_handling))]
impl ToU32String for U32String {
    #[inline]
    fn to_string(&self) -> U32String {
        self.to_owned()
    }
}

impl AsRef<u32str> for U32String {
    #[inline]
    fn as_ref(&self) -> &u32str {
        self
    }
}

impl AsMut<u32str> for U32String {
    #[inline]
    fn as_mut(&mut self) -> &mut u32str {
        self
    }
}

impl AsRef<[char]> for U32String {
    #[inline]
    fn as_ref(&self) -> &[char] {
        &self.vec
    }
}

#[cfg(not(no_global_oom_handling))]
impl From<&u32str> for U32String {
    /// Converts a `&str` into a [`U32String`].
    ///
    /// The result is allocated on the heap.
    #[inline]
    fn from(s: &u32str) -> U32String {
        s.to_owned()
    }
}

#[cfg(not(no_global_oom_handling))]
impl From<&mut u32str> for U32String {
    /// Converts a `&mut str` into a [`U32String`].
    ///
    /// The result is allocated on the heap.
    #[inline]
    fn from(s: &mut u32str) -> U32String {
        s.to_owned()
    }
}

#[cfg(not(no_global_oom_handling))]
impl From<&U32String> for U32String {
    /// Converts a `&U32String` into a [`U32String`].
    ///
    /// This clones `s` and returns the clone.
    #[inline]
    fn from(s: &U32String) -> U32String {
        s.clone()
    }
}

// TODO: Implement
// // note: test pulls in libstd, which causes errors here
// #[cfg(not(test))]
// impl From<Box<u32str>> for U32String {
//     /// Converts the given boxed `str` slice to a [`U32String`].
//     /// It is notable that the `str` slice is owned.
//     ///
//     /// # Examples
//     ///
//     /// Basic usage:
//     ///
//     /// ```
//     /// let s1: U32String = U32String::from("hello world");
//     /// let s2: Box<str> = s1.into_boxed_str();
//     /// let s3: U32String = U32String::from(s2);
//     ///
//     /// assert_eq!("hello world", s3)
//     /// ```
//     fn from(s: Box<u32str>) -> U32String {
//
//         s.into_string()
//     }
// }

#[cfg(not(no_global_oom_handling))]
impl From<U32String> for Box<u32str> {
    /// Converts the given [`U32String`] to a boxed `str` slice that is owned.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let s1: U32String = U32String::from("hello world");
    /// let s2: Box<str> = Box::from(s1);
    /// let s3: U32String = U32String::from(s2);
    ///
    /// assert_eq!("hello world", s3)
    /// ```
    fn from(s: U32String) -> Box<u32str> {
        s.into_boxed_u32str()
    }
}

#[cfg(not(no_global_oom_handling))]
impl<'a> From<Cow<'a, u32str>> for U32String {
    /// Converts a clone-on-write string to an owned
    /// instance of [`U32String`].
    ///
    /// This extracts the owned string,
    /// clones the string if it is not already owned.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::borrow::Cow;
    /// // If the string is not owned...
    /// let cow: Cow<str> = Cow::Borrowed("eggplant");
    /// // It will allocate on the heap and copy the string.
    /// let owned: U32String = U32String::from(cow);
    /// assert_eq!(&owned[..], "eggplant");
    /// ```
    fn from(s: Cow<'a, u32str>) -> U32String {
        s.into_owned()
    }
}

#[cfg(not(no_global_oom_handling))]
impl<'a> From<&'a u32str> for Cow<'a, u32str> {
    /// Converts a string slice into a [`Borrowed`] variant.
    /// No heap allocation is performed, and the string
    /// is not copied.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::borrow::Cow;
    /// assert_eq!(Cow::from("eggplant"), Cow::Borrowed("eggplant"));
    /// ```
    ///
    /// [`Borrowed`]: crate::borrow::Cow::Borrowed "borrow::Cow::Borrowed"
    #[inline]
    fn from(s: &'a u32str) -> Cow<'a, u32str> {
        Cow::Borrowed(s)
    }
}

#[cfg(not(no_global_oom_handling))]
impl<'a> From<U32String> for Cow<'a, u32str> {
    /// Converts a [`U32String`] into an [`Owned`] variant.
    /// No heap allocation is performed, and the string
    /// is not copied.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::borrow::Cow;
    /// let s = "eggplant".to_string();
    /// let s2 = "eggplant".to_string();
    /// assert_eq!(Cow::from(s), Cow::<'static, str>::Owned(s2));
    /// ```
    ///
    /// [`Owned`]: crate::borrow::Cow::Owned "borrow::Cow::Owned"
    #[inline]
    fn from(s: U32String) -> Cow<'a, u32str> {
        Cow::Owned(s)
    }
}

#[cfg(not(no_global_oom_handling))]
impl<'a> From<&'a U32String> for Cow<'a, u32str> {
    /// Converts a [`U32String`] reference into a [`Borrowed`] variant.
    /// No heap allocation is performed, and the string
    /// is not copied.
    ///
    /// # Example
    ///
    /// ```
    /// # use std::borrow::Cow;
    /// let s = "eggplant".to_string();
    /// assert_eq!(Cow::from(&s), Cow::Borrowed("eggplant"));
    /// ```
    ///
    /// [`Borrowed`]: crate::borrow::Cow::Borrowed "borrow::Cow::Borrowed"
    #[inline]
    fn from(s: &'a U32String) -> Cow<'a, u32str> {
        Cow::Borrowed(s.as_u32str())
    }
}

// TODO: Figure out how to do this...
// #[cfg(not(no_global_oom_handling))]
// impl<'a> FromIterator<char> for Cow<'a, u32str> {
//     fn from_iter<I: IntoIterator<Item = char>>(it: I) -> Cow<'a, u32str> {
//         Cow::Owned(FromIterator::from_iter(it))
//     }
// }

#[cfg(not(no_global_oom_handling))]
impl<'a, 'b> FromIterator<&'b u32str> for Cow<'a, u32str> {
    fn from_iter<I: IntoIterator<Item = &'b u32str>>(it: I) -> Cow<'a, u32str> {
        Cow::Owned(FromIterator::from_iter(it))
    }
}

#[cfg(not(no_global_oom_handling))]
impl<'a> FromIterator<U32String> for Cow<'a, u32str> {
    fn from_iter<I: IntoIterator<Item = U32String>>(it: I) -> Cow<'a, u32str> {
        Cow::Owned(FromIterator::from_iter(it))
    }
}

// TODO: Implement
// impl From<U32String> for Vec<u8> {
//     /// Converts the given [`U32String`] to a vector [`Vec`] that holds values of type [`u8`].
//     ///
//     /// # Examples
//     ///
//     /// Basic usage:
//     ///
//     /// ```
//     /// let s1 = U32String::from("hello world");
//     /// let v1 = Vec::from(s1);
//     ///
//     /// for b in v1 {
//     ///     println!("{b}");
//     /// }
//     /// ```
//     fn from(string: U32String) -> Vec<u8> {
//         string.into_bytes()
//     }
// }

#[cfg(not(no_global_oom_handling))]
impl fmt::Write for U32String {
    #[inline]
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.push_str(s);
        Ok(())
    }

    #[inline]
    fn write_char(&mut self, c: char) -> fmt::Result {
        self.push(c);
        Ok(())
    }
}

/// A draining iterator for `U32String`.
///
/// This struct is created by the [`drain`] method on [`U32String`]. See its
/// documentation for more.
///
/// [`drain`]: U32String::drain
pub struct Drain<'a> {
    /// Will be used as &'a mut U32String in the destructor
    string: *mut U32String,
    /// Start of part to remove
    start: usize,
    /// End of part to remove
    end: usize,
    /// Current remaining range to remove
    iter: Chars<'a>,
}

impl fmt::Debug for Drain<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Drain").field(&self.as_str()).finish()
    }
}

unsafe impl Sync for Drain<'_> {}
unsafe impl Send for Drain<'_> {}

impl Drop for Drain<'_> {
    fn drop(&mut self) {
        unsafe {
            // Use Vec::drain. "Reaffirm" the bounds checks to avoid
            // panic code being inserted again.
            let self_vec = (*self.string).as_mut_vec();
            if self.start <= self.end && self.end <= self_vec.len() {
                self_vec.drain(self.start..self.end);
            }
        }
    }
}

impl<'a> Drain<'a> {
    /// Returns the remaining (sub)string of this iterator as a slice.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut s = U32String::from("abc");
    /// let mut drain = s.drain(..);
    /// assert_eq!(drain.as_str(), "abc");
    /// let _ = drain.next().unwrap();
    /// assert_eq!(drain.as_str(), "bc");
    /// ```
    #[must_use]
    pub fn as_str(&self) -> &str {
        self.iter.as_str()
    }
}

impl<'a> AsRef<str> for Drain<'a> {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl<'a> AsRef<[u8]> for Drain<'a> {
    fn as_ref(&self) -> &[u8] {
        self.as_str().as_bytes()
    }
}

impl Iterator for Drain<'_> {
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<char> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    #[inline]
    fn last(mut self) -> Option<char> {
        self.next_back()
    }
}

impl DoubleEndedIterator for Drain<'_> {
    #[inline]
    fn next_back(&mut self) -> Option<char> {
        self.iter.next_back()
    }
}

impl FusedIterator for Drain<'_> {}

#[cfg(not(no_global_oom_handling))]
impl From<char> for U32String {
    /// Allocates an owned [`U32String`] from a single character.
    ///
    /// # Example
    /// ```rust
    /// let c: char = 'a';
    /// let s: U32String = U32String::from(c);
    /// assert_eq!("a", &s[..]);
    /// ```
    #[inline]
    fn from(c: char) -> Self {
        U32String::from(c)
    }
}
