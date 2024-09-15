use vstd::prelude::*;

use super::len::*;
use super::vest::*;
use super::depend::*;
use super::tag::*;

verus! {

/// Combainator for OCTET STRING in ASN.1
pub struct OctetString;

impl View for OctetString {
    type V = OctetString;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl ASN1Tagged for OctetString {
    open spec fn spec_tag(&self) -> TagValue {
        TagValue {
            class: TagClass::Universal,
            form: TagForm::Primitive,
            num: 0x04,
        }
    }

    fn tag(&self) -> TagValue {
        TagValue {
            class: TagClass::Universal,
            form: TagForm::Primitive,
            num: 0x04,
        }
    }
}

impl ViewWithASN1Tagged for OctetString {
    proof fn lemma_view_preserves_tag(&self) {}
}

impl SpecCombinator for OctetString {
    type SpecResult = Seq<u8>;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        match new_spec_octet_string_inner().spec_parse(s) {
            Ok((len, (_, v))) => Ok((len, v)),
            Err(..) => Err(()),
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {}

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        new_spec_octet_string_inner().spec_serialize((v.len() as LengthValue, v))
    }
}

impl SecureSpecCombinator for OctetString {
    open spec fn spec_is_prefix_secure() -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        new_spec_octet_string_inner().theorem_serialize_parse_roundtrip((v.len() as LengthValue, v));
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        new_spec_octet_string_inner().theorem_parse_serialize_roundtrip(buf);
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        new_spec_octet_string_inner().lemma_prefix_secure(s1, s2);
    }
}

impl Combinator for OctetString {
    type Result<'a> = &'a [u8];
    type Owned = Vec<u8>;

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
        if let Ok((len, (_, v))) = new_octet_string_inner().parse(s) {
            Ok((len, v))
        } else {
            Err(())
        }
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, ()>) {
        new_octet_string_inner().serialize((v.len() as LengthValue, v), data, pos)
    }
}

/// The function |i| Bytes(i)
struct BytesCont;

impl Continuation for BytesCont {
    type Input<'a> = LengthValue;
    type Output = Bytes;

    fn apply<'a>(&self, i: Self::Input<'a>) -> (o: Self::Output) {
        Bytes(i as usize)
    }

    open spec fn requires<'a>(&self, i: Self::Input<'a>) -> bool {
        true
    }

    open spec fn ensures<'a>(&self, i: Self::Input<'a>, o: Self::Output) -> bool {
        o == Bytes(i as usize)
    }
}

type SpecOctetStringInner = SpecDepend<Length, Bytes>;
type OctetStringInner = Depend<Length, Bytes, BytesCont>;

pub open spec fn new_spec_octet_string_inner() -> SpecOctetStringInner {
    SpecDepend {
        fst: Length,
        snd: |l| {
            Bytes(l as usize)
        },
    }
}

fn new_octet_string_inner() -> (res: OctetStringInner)
    ensures res@ == new_spec_octet_string_inner()
{
    Depend {
        fst: Length,
        snd: BytesCont,
        spec_snd: Ghost(|l| {
            Bytes(l as usize)
        }),
    }
}

}
