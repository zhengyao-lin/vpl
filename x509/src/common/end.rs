use vstd::prelude::*;
use crate::utils::*;
use super::vest::*;

verus! {

/// A combinator that only matches the end of the buffer
#[derive(Debug)]
pub struct End;
impl_trivial_view!(End);

impl SpecCombinator for End {
    type SpecResult = ();

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        if s.len() == 0 {
            Ok((0, ()))
        } else {
            Err(())
        }
    }

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        Ok(seq![])
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {}
}

impl SecureSpecCombinator for End {
    open spec fn spec_is_prefix_secure() -> bool {
        false
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {}

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        let empty: Seq<u8> = seq![];
        assert(buf.subrange(0, 0) == empty);
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {}
}

impl Combinator for End {
    type Result<'a> = ();
    type Owned = ();

    open spec fn spec_length(&self) -> Option<usize> {
        Some(0)
    }

    fn length(&self) -> Option<usize> {
        Some(0)
    }

    fn exec_is_prefix_secure() -> bool {
        false
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ()>) {
        if s.len() == 0 {
            Ok((0, ()))
        } else {
            Err(())
        }
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, ()>) {
        if pos < data.len() {
            let ghost empty: Seq<u8> = seq![];
            assert(data@ =~= seq_splice(old(data)@, pos, empty));
            Ok(0)
        } else {
            Err(())
        }
    }
}

}
