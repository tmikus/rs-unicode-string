use crate::{u32str, U32String};
use std::borrow::Cow;

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
// note: test pulls in libstd, which causes errors here
#[cfg(not(test))]
impl From<Box<u32str>> for U32String {
    /// Converts the given boxed `str` slice to a [`U32String`].
    /// It is notable that the `str` slice is owned.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use u32_string::U32String;
    ///
    /// let s1: U32String = U32String::from("hello world");
    /// let s2: Box<str> = s1.into_boxed_str();
    /// let s3: U32String = U32String::from(s2);
    ///
    /// assert_eq!("hello world", s3)
    /// ```
    fn from(s: Box<u32str>) -> U32String {
        s.into_u32string()
    }
}

impl From<Vec<char>> for U32String {
    fn from(vec: Vec<char>) -> Self {
        U32String { vec }
    }
}

#[cfg(not(no_global_oom_handling))]
impl From<U32String> for Box<u32str> {
    /// Converts the given [`U32String`] to a boxed `str` slice that is owned.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use u32_macros::ustr;
    /// use u32_string::{u32str, U32String};
    ///
    /// let s1: U32String = U32String::from("hello world");
    /// let s2: Box<u32str> = Box::from(s1);
    /// let s3: U32String = U32String::from(s2);
    ///
    /// assert_eq!(ustr!("hello world"), s3)
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
    /// use u32_string::{ustr, u32str, U32String};
    ///
    /// // If the string is not owned...
    /// let cow: Cow<u32str> = Cow::Borrowed(ustr!("eggplant"));
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
    /// use u32_string::ustr;
    ///
    /// assert_eq!(Cow::from(ustr!("eggplant")), Cow::Borrowed(ustr!("eggplant")));
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
    /// use u32_string::{ToU32String, ustr, u32str};
    ///
    /// let s = ustr!("eggplant").to_u32string();
    /// let s2 = ustr!("eggplant").to_u32string();
    /// assert_eq!(Cow::from(s), Cow::<'static, u32str>::Owned(s2));
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
    /// use u32_string::{ToU32String, ustr};
    ///
    /// let s = ustr!("eggplant").to_u32string();
    /// assert_eq!(Cow::from(&s), Cow::Borrowed(ustr!("eggplant")));
    /// ```
    ///
    /// [`Borrowed`]: crate::borrow::Cow::Borrowed "borrow::Cow::Borrowed"
    #[inline]
    fn from(s: &'a U32String) -> Cow<'a, u32str> {
        Cow::Borrowed(s.as_u32str())
    }
}

#[cfg(not(no_global_oom_handling))]
impl From<char> for U32String {
    /// Allocates an owned [`U32String`] from a single character.
    ///
    /// # Example
    /// ```rust
    /// use u32_string::U32String;
    ///
    /// let c: char = 'a';
    /// let s: U32String = U32String::from(c);
    /// assert_eq!("a", &s[..]);
    /// ```
    #[inline]
    fn from(c: char) -> Self {
        U32String::from(c)
    }
}

impl From<&str> for U32String {
    /// Creates a new [`U32String`] from an existing [`&str`].
    /// It copies the data from the [`&str`] to a new instance of [`U32String`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use u32_string::U32String;
    ///
    /// let text = "example str";
    /// let u32_text = U32String::from(text);
    ///
    /// assert_eq!(text, u32_text);
    /// ```
    #[inline]
    fn from(value: &str) -> U32String {
        U32String::from(value.chars().collect::<Vec<char>>())
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
