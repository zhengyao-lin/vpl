/// Define and implement a temporary Eq replacement "PolyfillEq" for some types

use vstd::prelude::*;

use super::*;

verus! {

/// A temporary replacement Clone
pub trait PolyfillEq: View + Sized {
    fn polyfill_eq(&self, other: &Self) -> (res: bool)
        ensures
            res <==> (self@ == other@);
}

macro_rules! impl_trivial_polyfill_eq {
    ($($t:ty)*) => {
        $(
            ::builtin_macros::verus! {
                impl PolyfillEq for $t {
                    fn polyfill_eq(&self, other: &Self) -> bool {
                        self == other
                    }
                }
            }
        )*
    };
}

impl_trivial_polyfill_eq! {
    bool
    u8 u16 u32 u64 u128
    i8 i16 i32 i64 i128
    usize
}

}
