use crate::{u32str, U32String};
use std::borrow::Cow;

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
