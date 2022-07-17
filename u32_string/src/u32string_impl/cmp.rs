use crate::{u32str, U32String};
use std::borrow::Cow;

impl PartialEq for U32String {
    #[inline]
    fn eq(&self, other: &U32String) -> bool {
        println!("U32String.eq");
        PartialEq::eq(&self[..], &other[..])
    }
    #[inline]
    fn ne(&self, other: &U32String) -> bool {
        println!("U32String.ne");
        PartialEq::ne(&self[..], &other[..])
    }
}

macro_rules! impl_eq {
    ($lhs:ty, $rhs: ty) => {
        #[allow(unused_lifetimes)]
        impl<'a, 'b> PartialEq<$rhs> for $lhs {
            #[inline]
            fn eq(&self, other: &$rhs) -> bool {
                println!("U32String.eq");
                PartialEq::eq(&self[..], &other[..])
            }
            #[inline]
            fn ne(&self, other: &$rhs) -> bool {
                println!("U32String.ne");
                PartialEq::ne(&self[..], &other[..])
            }
        }

        #[allow(unused_lifetimes)]
        impl<'a, 'b> PartialEq<$lhs> for $rhs {
            #[inline]
            fn eq(&self, other: &$lhs) -> bool {
                println!("U32String.eq");
                PartialEq::eq(&self[..], &other[..])
            }
            #[inline]
            fn ne(&self, other: &$lhs) -> bool {
                println!("U32String.ne");
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
