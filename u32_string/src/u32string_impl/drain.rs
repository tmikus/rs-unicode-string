// use crate::U32String;
// use std::fmt;
// use std::iter::FusedIterator;
// use std::str::Chars;
//
// /// A draining iterator for `U32String`.
// ///
// /// This struct is created by the [`drain`] method on [`U32String`]. See its
// /// documentation for more.
// ///
// /// [`drain`]: U32String::drain
// pub struct Drain<'a> {
//     /// Will be used as &'a mut U32String in the destructor
//     string: *mut U32String,
//     /// Start of part to remove
//     start: usize,
//     /// End of part to remove
//     end: usize,
//     /// Current remaining range to remove
//     iter: Chars<'a>,
// }
//
// impl fmt::Debug for Drain<'_> {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         f.debug_tuple("Drain").field(&self.as_str()).finish()
//     }
// }
//
// unsafe impl Sync for Drain<'_> {}
// unsafe impl Send for Drain<'_> {}
//
// impl Drop for Drain<'_> {
//     fn drop(&mut self) {
//         unsafe {
//             // Use Vec::drain. "Reaffirm" the bounds checks to avoid
//             // panic code being inserted again.
//             let self_vec = (*self.string).as_mut_vec();
//             if self.start <= self.end && self.end <= self_vec.len() {
//                 self_vec.drain(self.start..self.end);
//             }
//         }
//     }
// }
//
// impl<'a> Drain<'a> {
//     /// Returns the remaining (sub)string of this iterator as a slice.
//     ///
//     /// # Examples
//     ///
//     /// ```
//     /// use u32_string::U32String;
//     ///
//     /// let mut s = U32String::from("abc");
//     /// let mut drain = s.drain(..);
//     /// assert_eq!(drain.as_str(), "abc");
//     /// let _ = drain.next().unwrap();
//     /// assert_eq!(drain.as_str(), "bc");
//     /// ```
//     #[must_use]
//     pub fn as_str(&self) -> &str {
//         self.iter.as_str()
//     }
// }
//
// impl<'a> AsRef<str> for Drain<'a> {
//     fn as_ref(&self) -> &str {
//         self.as_str()
//     }
// }
//
// impl<'a> AsRef<[u8]> for Drain<'a> {
//     fn as_ref(&self) -> &[u8] {
//         self.as_str().as_bytes()
//     }
// }
//
// impl Iterator for Drain<'_> {
//     type Item = char;
//
//     #[inline]
//     fn next(&mut self) -> Option<char> {
//         self.iter.next()
//     }
//
//     fn size_hint(&self) -> (usize, Option<usize>) {
//         self.iter.size_hint()
//     }
//
//     #[inline]
//     fn last(mut self) -> Option<char> {
//         self.next_back()
//     }
// }
//
// impl DoubleEndedIterator for Drain<'_> {
//     #[inline]
//     fn next_back(&mut self) -> Option<char> {
//         self.iter.next_back()
//     }
// }
//
// impl FusedIterator for Drain<'_> {}
