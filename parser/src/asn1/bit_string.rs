use std::fmt::{self, Debug, Formatter};
use vstd::prelude::*;
use vstd::std_specs::bits::u8_trailing_zeros;

use polyfill::*;

use crate::common::*;

use super::octet_string::*;
use super::tag::*;

verus! {

/// Combainator for BIT STRING in ASN.1
/// Essentially a refined version of OctetString
/// where we require that the first bit correctly
/// specifies the trailing zeros
#[derive(Debug, View)]
pub struct BitString;

asn1_tagged!(BitString, tag_of!(BIT_STRING));

// #[derive(View, PolyfillClone)]
// pub struct BitStringValuePoly<T>(pub T);

pub type SpecBitStringValue = Seq<u8>;

pub struct BitStringValue<'a>(&'a [u8]);
pub struct BitStringValueOwned(Vec<u8>);

impl<'a> PolyfillClone for BitStringValue<'a> {
    fn clone(&self) -> Self {
        proof {
            use_type_invariant(self);
        }
        BitStringValue(&self.0)
    }
}

impl<'a> View for BitStringValue<'a> {
    type V = Seq<u8>;

    closed spec fn view(&self) -> Self::V {
        self.0@
    }
}

impl View for BitStringValueOwned {
    type V = Seq<u8>;

    closed spec fn view(&self) -> Self::V {
        self.0@
    }
}

impl<'a> BitStringValue<'a> {
    #[verifier::type_invariant]
    closed spec fn inv(self) -> bool {
        Self::spec_wf(self@)
    }

    pub open spec fn spec_wf(s: SpecBitStringValue) -> bool {
        // Empty string
        ||| s.len() == 1 && s[0] == 0

        // Otherwise, check that all trailing bits (as declared in bytes[0]) are zeros
        ||| s.len() > 1 && s[0] <= u8_trailing_zeros(s.last())
    }

    pub fn wf(s: &'a [u8]) -> (res: bool)
        ensures res == Self::spec_wf(s@)
    {
        s.len() == 1 && s[0] == 0
        || s.len() > 1 && s[0] as u32 <= s[s.len() - 1].trailing_zeros()
    }

    /// Create a BitString from raw bytes
    /// The first byte of the slice should indicate the number of trailing zeros
    pub fn new_raw(s: &'a [u8]) -> (res: Option<BitStringValue<'a>>)
        ensures
            res matches Some(res) ==> res@ == s@ && Self::spec_wf(res@),
            res.is_none() ==> !Self::spec_wf(s@)
    {
        if Self::wf(s) {
            Some(BitStringValue(s))
        } else {
            None
        }
    }

    /// Get the number of padded zeros at the end
    pub fn trailing_zeros(&self) -> u8
    {
        proof {
            use_type_invariant(self);
        }
        self.0[self.0.len() - 1]
    }

    /// Get the actual (padded) bit string
    pub fn bit_string(&self) -> (res: &[u8])
        ensures res@ == self@.drop_first()
    {
        proof {
            use_type_invariant(self);
        }
        slice_drop_first(self.0)
    }
}

impl SpecCombinator for BitString {
    type SpecResult = SpecBitStringValue;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        match OctetString.spec_parse(s) {
            Ok((len, bytes)) =>
                if BitStringValue::spec_wf(bytes) {
                    Ok((len, bytes))
                } else {
                    Err(())
                }

            Err(..) => Err(()),
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {}

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        if BitStringValue::spec_wf(v) {
            OctetString.spec_serialize(v)
        } else {
            Err(())
        }
    }
}

impl SecureSpecCombinator for BitString {
    open spec fn is_prefix_secure() -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        OctetString.theorem_serialize_parse_roundtrip(v);
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

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        let (len, v) = OctetString.parse(s)?;

        if let Some(s) = BitStringValue::new_raw(v) {
            Ok((len, s))
        } else {
            Err(ParseError::Other("Ill-formed bit string".to_string()))
        }
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        proof {
            use_type_invariant(&v);
        }
        OctetString.serialize(v.0, data, pos)
    }
}

}

impl<'a> Debug for BitStringValue<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "BitStringValue([{}] ", (self.0.len() - 1) * 8 - self.0[0] as usize)?;

        // Print the hex values
        for i in 1..self.0.len() {
            write!(f, "{:02x}", self.0[i])?;
        }

        write!(f, ")")
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use der::Encode;

    fn serialize_bit_string(v: BitStringValue) -> Result<Vec<u8>, SerializeError> {
        let mut data = vec![0; v.bit_string().len() + 10];
        data[0] = 0x03; // Prepend the tag byte
        let len = BitString.serialize(v, &mut data, 1)?;
        data.truncate(len + 1);
        Ok(data)
    }

    #[test]
    fn diff_with_der() {
        // The first byte of raw should denote the number of trailing zeros
        let diff = |raw: &[u8]| {
            let res1 = serialize_bit_string(BitStringValue::new_raw(raw).unwrap()).map_err(|_| ());
            let res2 = der::asn1::BitString::new(raw[0], &raw[1..]).unwrap().to_der().map_err(|_| ());
            assert_eq!(res1, res2);
        };

        diff(&[0]);
        diff(&[5, 0b11100000]);
        diff(&[4, 0b11100000]);
    }
}
