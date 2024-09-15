use vstd::prelude::*;
use vstd::std_specs::bits::u8_trailing_zeros;

use polyfill::*;

use super::vest::*;
use super::octet_string::*;
use super::tag::*;

verus! {

pub struct SpecBitStringValue(pub Seq<u8>);
pub struct BitStringValue<'a>(&'a [u8]);
pub struct BitStringValueOwned(Vec<u8>);

/// Combainator for BIT STRING in ASN.1
/// Essentially a refined version of OctetString
/// where we require that the first bit correctly
/// specifies the trailing zeros
pub struct BitString;

impl View for BitString {
    type V = BitString;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl<'a> View for BitStringValue<'a> {
    type V = SpecBitStringValue;

    closed spec fn view(&self) -> Self::V {
        SpecBitStringValue(self.0@)
    }
}

impl View for BitStringValueOwned {
    type V = SpecBitStringValue;

    closed spec fn view(&self) -> Self::V {
        SpecBitStringValue(self.0@)
    }
}

impl ASN1Tagged for BitString {
    open spec fn spec_tag(&self) -> TagValue {
        TagValue {
            class: TagClass::Universal,
            form: TagForm::Primitive,
            num: 0x03,
        }
    }

    fn tag(&self) -> TagValue {
        TagValue {
            class: TagClass::Universal,
            form: TagForm::Primitive,
            num: 0x03,
        }
    }
}

impl ViewWithASN1Tagged for BitString {
    proof fn lemma_view_preserves_tag(&self) {}
}

impl SpecBitStringValue {
    pub open spec fn wf(&self) -> bool {
        // Empty string
        ||| self.0.len() == 1 && self.0[0] == 0

        // Otherwise, check that all trailing bits (as declared in bytes[0]) are zeros
        ||| self.0.len() > 1 && self.0[0] <= u8_trailing_zeros(self.0.last())
    }
}

impl<'a> BitStringValue<'a> {
    pub fn wf(&self) -> (res: bool)
        ensures res == self@.wf()
    {
        self.0.len() == 1 && self.0[0] == 0
        || self.0.len() > 1 && self.0[0] as u32 <= self.0[self.0.len() - 1].trailing_zeros()
    }

    pub fn new_raw(s: &'a [u8]) -> (res: Option<BitStringValue<'a>>)
        ensures res.is_some() ==> res.unwrap()@.wf()
    {
        let res = BitStringValue(s);

        if res.wf() {
            Some(res)
        } else {
            None
        }
    }

    /// Get the number of padded zeros at the end
    pub fn trailing_zeros(&self) -> u8
    {
        if self.0.len() == 0 {
            0
        } else {
            self.0[self.0.len() - 1]
        }
    }

    /// Get the actual (padded) bit string
    pub fn bit_string(&self) -> &[u8]
        requires self@.wf()
    {
        if self.0.len() == 0 {
            self.0
        } else {
            slice_drop_first(self.0)
        }
    }
}

impl SpecCombinator for BitString {
    type SpecResult = SpecBitStringValue;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        match OctetString.spec_parse(s) {
            Ok((len, bytes)) =>
                if SpecBitStringValue(bytes).wf() {
                    Ok((len, SpecBitStringValue(bytes)))
                } else {
                    Err(())
                }

            Err(..) => Err(()),
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {}

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        if v.wf() {
            OctetString.spec_serialize(v.0)
        } else {
            Err(())
        }
    }
}

impl SecureSpecCombinator for BitString {
    open spec fn spec_is_prefix_secure() -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        OctetString.theorem_serialize_parse_roundtrip(v.0);
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        OctetString.theorem_parse_serialize_roundtrip(buf);
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        OctetString.lemma_prefix_secure(s1, s2);
    }
}

impl Combinator for BitString {
    type Result<'a> = BitStringValue<'a>;
    type Owned = BitStringValueOwned;

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
        let (len, v) = OctetString.parse(s)?;

        if BitStringValue(v).wf() {
            Ok((len, BitStringValue(v)))
        } else {
            Err(())
        }
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, ()>) {
        if v.wf() {
            OctetString.serialize(v.0, data, pos)
        } else {
            Err(())
        }
    }
}

}
