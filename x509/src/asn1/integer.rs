use vstd::prelude::*;

use crate::polyfill::*;
use crate::vest::*;
use crate::asn1::*;

verus! {

/// A vest::Pred that checks if given (n: u64, v: i64)
/// n is the minimum number of bytes required to represent v
pub struct MinimalInt;

impl View for MinimalInt {
    type V = MinimalInt;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecPred for MinimalInt {
    type Input = (VarUIntResult, VarIntResult);

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let (n, v) = *i;

        // Enforce some additional rules in DER:
        // 1. At least 1 byte is required (even if v == 0)
        // 2. v as a signed integer can fit into n bytes
        // 3. v as a signed integer cannot fit into (n - 1) bytes
        0 < n && n <= var_uint_size!() &&
        n_byte_min_signed!(n) <= v <= n_byte_max_signed!(n) &&
        (v == 0 || !(n_byte_min_signed!(n - 1) <= v <= n_byte_max_signed!(n - 1)))
    }
}

impl Pred for MinimalInt {
    type Input<'a> = (VarUIntResult, VarIntResult);
    type InputOwned = (VarUIntResult, VarIntResult);

    fn apply(&self, i: &Self::Input<'_>) -> bool {
        let (n, v) = *i;

        n > 0 && n <= var_uint_size!() &&
        n_byte_min_signed!(n) <= v && v <= n_byte_max_signed!(n) &&
        (v == 0 || !(n_byte_min_signed!(n - 1) <= v && v <= n_byte_max_signed!(n - 1)))
    }
}

pub struct IntegerCont;

impl Continuation for IntegerCont {
    type Input<'a> = VarUIntResult;
    type Output = VarInt;

    fn apply<'a>(&self, i: Self::Input<'a>) -> (o: Self::Output) {
        VarInt(i as usize)
    }

    open spec fn requires<'a>(&self, i: Self::Input<'a>) -> bool {
        true
    }

    open spec fn ensures<'a>(&self, i: Self::Input<'a>, o: Self::Output) -> bool {
        o == VarInt(i as usize)
    }
}

pub struct Integer;
pub type IntegerInner = Refined<
    Depend<Preceded<Tag<U8, u8>, Length>, VarInt, IntegerCont>,
    MinimalInt,
>;

impl Integer {
    pub fn new() -> IntegerInner {
        let ghost spec_snd = |l| {
            VarInt(l as usize)
        };
    
        let inner = Depend {
            fst: Preceded(Tag::new(U8, 0x02), Length),
            snd: IntegerCont,
            spec_snd: Ghost(spec_snd),
        };
    
        Refined {
            inner,
            predicate: MinimalInt,
        }
    }
}

}
