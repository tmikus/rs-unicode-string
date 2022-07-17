use crate::{u32str, U32String};
use std::ops;

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
        &self
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
        unsafe { u32str::from_char_unchecked_mut(&mut *self.vec) }
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
