// #[cfg(not(no_global_oom_handling))]
// impl FromStr for U32String {
//     type Err = core::convert::Infallible;
//     #[inline]
//     fn from_str(s: &str) -> Result<U32String, Self::Err> {
//         Ok(U32String::from(s))
//     }
// }

use crate::{u32str, U32String};
use std::fmt;

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
    /// use u32_string::{ToU32String, U32String};
    ///
    /// let i = 5;
    /// let five = U32String::from("5");
    ///
    /// assert_eq!(five, i.to_u32string());
    /// ```
    #[rustc_conversion_suggestion]
    fn to_u32string(&self) -> U32String;
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
    default fn to_u32string(&self) -> U32String {
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
    fn to_u32string(&self) -> U32String {
        U32String::from(*self)
    }
}

#[cfg(not(no_global_oom_handling))]
impl ToU32String for u8 {
    #[inline]
    fn to_u32string(&self) -> U32String {
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
    fn to_u32string(&self) -> U32String {
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
    fn to_u32string(&self) -> U32String {
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
    fn to_u32string(&self) -> U32String {
        self.to_owned()
    }
}
