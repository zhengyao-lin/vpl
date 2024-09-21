use std::fmt::{self, Debug, Formatter};
use vstd::prelude::*;

use crate::common::*;

use super::octet_string::*;
use super::tag::*;

verus! {

/// If it's expected that an INTEGER field is larger than the Int type,
/// then use this combinator to read it as an octet string (with
/// some minimality constraints).
#[derive(Debug, View)]
pub struct BigInt;

asn1_tagged!(BigInt, TagValue {
    class: TagClass::Universal,
    form: TagForm::Primitive,
    num: 0x02,
});

/// BigInt represents the integer with a sequence of bytes in big-endian order
/// (same as ASN.1) and the most significant bit of the first byte is the sign bit.
pub type SpecBigIntValue = Seq<u8>;
pub struct BigIntValue<'a>(&'a [u8]);
pub struct BigIntOwned(Vec<u8>);

impl<'a> View for BigIntValue<'a> {
    type V = Seq<u8>;

    closed spec fn view(&self) -> Self::V {
        self.0@
    }
}

impl View for BigIntOwned {
    type V = Seq<u8>;

    closed spec fn view(&self) -> Self::V {
        self.0@
    }
}

impl<'a> PolyfillClone for BigIntValue<'a> {
    fn clone(&self) -> Self {
        BigIntValue(&self.0)
    }
}

impl<'a> BigIntValue<'a> {
    /// `bytes` should be the minimal encoding
    /// i.e. the first byte should not be 0 unless
    ///   1. bytes.len() == 1
    ///   2. bytes[1] >= 0x80
    pub open spec fn spec_wf(bytes: Seq<u8>) -> bool {
        &&& bytes.len() != 0
        &&& bytes[0] == 0 ==> {
            ||| bytes.len() == 1
            // the first byte cannot be removed, otherwise it will turn into a negative number
            ||| bytes[1] >= 0x80
        }
    }

    pub fn wf(bytes: &'a [u8]) -> (res: bool)
        ensures res == BigIntValue::spec_wf(bytes@)
    {
        bytes.len() != 0 &&
        (bytes[0] != 0 || bytes.len() == 1 || bytes[1] >= 0x80)
    }

    // TODO: add more methods to interpret BigIntValue as an integer
}

impl SpecCombinator for BigInt {
    type SpecResult = Seq<u8>;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        new_spec_big_int_inner().spec_parse(s)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {}

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        new_spec_big_int_inner().spec_serialize(v)
    }
}

impl SecureSpecCombinator for BigInt {
    open spec fn spec_is_prefix_secure() -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        new_spec_big_int_inner().theorem_serialize_parse_roundtrip(v);
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        new_spec_big_int_inner().theorem_parse_serialize_roundtrip(buf);
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        new_spec_big_int_inner().lemma_prefix_secure(s1, s2);
    }
}

impl Combinator for BigInt {
    type Result<'a> = BigIntValue<'a>;
    type Owned = BigIntOwned;

    open spec fn spec_length(&self) -> Option<usize> {
        None
    }

    fn length(&self) -> Option<usize> {
        None
    }

    fn exec_is_prefix_secure() -> bool {
        true
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ()>) {
        if let Ok((len, v)) = new_big_int_inner().parse(s) {
            Ok((len, BigIntValue(v)))
        } else {
            Err(())
        }
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, ()>) {
        new_big_int_inner().serialize(v.0, data, pos)
    }
}

/// A condition that the minimal encoding is used
pub struct MinimalBigInt;

impl View for MinimalBigInt {
    type V = MinimalBigInt;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecPred for MinimalBigInt {
    type Input = Seq<u8>;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        BigIntValue::spec_wf(*i)
    }
}

impl Pred for MinimalBigInt {
    type Input<'a> = &'a [u8];
    type InputOwned = Vec<u8>;

    fn apply(&self, i: &Self::Input<'_>) -> (res: bool)
    {
        BigIntValue::wf(i)
    }
}

type BigIntInner = Refined<OctetString, MinimalBigInt>;

pub open spec fn new_spec_big_int_inner() -> BigIntInner
{
    Refined {
        inner: OctetString,
        predicate: MinimalBigInt,
    }
}

fn new_big_int_inner() -> (res: BigIntInner)
    ensures res@ == new_spec_big_int_inner()
{
    Refined {
        inner: OctetString,
        predicate: MinimalBigInt,
    }
}

}

impl<'a> Debug for BigIntValue<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // Print self.0 as a big-endian big integer
        write!(f, "BigIntValue(0x")?;
        for b in self.0 {
            write!(f, "{:02x}", b)?;
        }
        write!(f, ")")
    }
}
