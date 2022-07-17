use crate::u32str;

impl PartialEq for u32str {
    #[inline]
    fn eq(&self, other: &u32str) -> bool {
        println!("u32str.eq");
        self.chars == other.chars
    }
    #[inline]
    fn ne(&self, other: &u32str) -> bool {
        println!("u32str.ne");
        !(*self).eq(other)
    }
}

impl Eq for u32str {}

/// Implements comparison operations on strings.
///
/// Strings are compared [lexicographically](Ord#lexicographical-comparison) by their byte values. This compares Unicode code
/// points based on their positions in the code charts. This is not necessarily the same as
/// "alphabetical" order, which varies by language and locale. Comparing strings according to
/// culturally-accepted standards requires locale-specific data that is outside the scope of
/// the `str` type.
impl PartialOrd for u32str {
    #[inline]
    fn partial_cmp(&self, other: &u32str) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for u32str {
    #[inline]
    fn cmp(&self, other: &u32str) -> std::cmp::Ordering {
        self.chars.cmp(&other.chars)
    }
}
