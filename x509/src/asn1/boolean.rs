use vstd::prelude::*;

use polyfill::*;

use crate::common::*;

use super::tag::*;

verus! {

/// Combainator for BOOLEAN in ASN.1
/// TRUE = 0x01 0x01 0xff
/// FALSE = 0x01 0x01 0x00
#[derive(Debug, View, ViewWithASN1Tagged)]
pub struct Boolean;

impl ASN1Tagged for Boolean {
    open spec fn spec_tag(&self) -> TagValue {
        TagValue {
            class: TagClass::Universal,
            form: TagForm::Primitive,
            num: 0x01,
        }
    }

    fn tag(&self) -> TagValue {
        TagValue {
            class: TagClass::Universal,
            form: TagForm::Primitive,
            num: 0x01,
        }
    }
}

impl SpecCombinator for Boolean {
    type SpecResult = bool;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        if s.len() < 3 {
            Err(())
        } else if s[0] == 0x01 && s[1] == 0x01 && s[2] == 0xff {
            Ok((3, true))
        } else if s[0] == 0x01 && s[1] == 0x01 && s[2] == 0x00 {
            Ok((3, false))
        } else {
            Err(())
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {}

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        if v {
            Ok(seq![ 0x01, 0x01, 0xff ])
        } else {
            Ok(seq![ 0x01, 0x01, 0x00 ])
        }
    }
}

impl SecureSpecCombinator for Boolean {
    open spec fn spec_is_prefix_secure() -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {}

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if let Ok((n, v)) = self.spec_parse(buf) {
            assert(self.spec_serialize(v).unwrap() =~= buf.subrange(0, 3));
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {}
}

impl Combinator for Boolean {
    type Result<'a> = bool;
    type Owned = bool;

    open spec fn spec_length(&self) -> Option<usize> {
        Some(3)
    }

    fn length(&self) -> Option<usize> {
        Some(3)
    }

    fn exec_is_prefix_secure() -> bool {
        true
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ()>) {
        if s.len() < 3 {
            Err(())
        } else if s[0] == 0x01 && s[1] == 0x01 && s[2] == 0xff {
            Ok((3, true))
        } else if s[0] == 0x01 && s[1] == 0x01 && s[2] == 0x00 {
            Ok((3, false))
        } else {
            Err(())
        }
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, ()>) {
        if pos > usize::MAX - 3 || pos + 3 > data.len() {
            return Err(());
        }

        if v {
            data.set(pos, 0x01);
            data.set(pos + 1, 0x01);
            data.set(pos + 2, 0xff);
        } else {
            data.set(pos, 0x01);
            data.set(pos + 1, 0x01);
            data.set(pos + 2, 0x00);
        }

        assert(data@ =~= seq_splice(old(data)@, pos, self@.spec_serialize(v@).unwrap()));

        Ok(3)
    }
}

}
