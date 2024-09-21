/// TODO: maybe refactor this using Refined

use std::fmt::{self, Debug, Formatter};
use vstd::prelude::*;

use polyfill::*;

use crate::common::*;

use super::octet_string::*;
use super::tag::*;

verus! {

/// Combinator for IA5String in ASN.1
/// Essentially a wrapper around Octet
/// that checks that each byte is <= 127
#[derive(Debug, View)]
pub struct IA5String;

asn1_tagged!(IA5String, TagValue {
    class: TagClass::Universal,
    form: TagForm::Primitive,
    num: 0x16,
});

#[derive(View, PolyfillClone)]
pub struct IA5StringPoly<T>(pub T);

pub type SpecIA5StringValue = IA5StringPoly<Seq<u8>>;
pub type IA5StringValue<'a> = IA5StringPoly<&'a [u8]>;
pub type IA5StringValueOwned = IA5StringPoly<Vec<u8>>;

impl SpecIA5StringValue {
    pub open spec fn wf(&self) -> bool {
        forall |i| 0 <= i < self.0.len() ==> self.0[i] <= 127
    }
}

impl<'a> IA5StringValue<'a> {
    pub fn new(s: &'a [u8]) -> (res: Option<IA5StringValue<'a>>)
        ensures
            res matches Some(res) ==> res@.wf(),
            res is None ==> !IA5StringPoly(s@).wf(),
    {
        let res = IA5StringPoly(s);

        if res.wf() {
            Some(res)
        } else {
            None
        }
    }

    pub fn as_bytes(&self) -> &'a [u8] {
        self.0
    }

    pub fn to_string(&self) -> Option<String> {
        match utf8_to_str(&self.0) {
            Some(s) => Some(s.to_string()),
            None => None,
        }
    }

    pub fn wf(&self) -> (res: bool)
        ensures res == self@.wf()
    {
        let len = self.0.len();
        for i in 0..len
            invariant
                len == self@.0.len(),
                forall |j| 0 <= j < i ==> self.0[j] <= 127,
        {
            if self.0[i] > 127 {
                return false;
            }
        }
        return true;
    }
}

impl SpecCombinator for IA5String {
    type SpecResult = SpecIA5StringValue;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        match OctetString.spec_parse(s) {
            Ok((len, v)) =>
                if IA5StringPoly(v).wf() {
                    Ok((len, IA5StringPoly(v)))
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

impl SecureSpecCombinator for IA5String {
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

impl Combinator for IA5String {
    type Result<'a> = IA5StringValue<'a>;
    type Owned = IA5StringValueOwned;

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

        if IA5StringPoly(v).wf() {
            Ok((len, IA5StringPoly(v)))
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

impl<'a> Debug for IA5StringValue<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.to_string() {
            Some(s) => write!(f, "IA5StringValue({:?})", s),
            None => write!(f, "IA5StringValue({:?})", self.0),
        }
    }
}
