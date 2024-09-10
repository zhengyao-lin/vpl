// A constant combinator that consumes nothing and returns a constant value

use vstd::prelude::*;

use crate::vest::*;
use crate::polyfill::*;

verus! {

pub struct Const<V>(pub V);

impl<V> View for Const<V> {
    type V = Const<V>;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

/// We assume that View impl for V is a trivial one
/// the type is the same, and view() should be identity
/// (assumed in Combinator::parse_requires and Combinator::serialize_requires)
impl<V: View<V = V> + Eq> SpecCombinator for Const<V> {
    type SpecResult = <V as vstd::string::View>::V;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        Ok((0, self.0))
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {}

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        // Can only serialize a constant with the same value (for properties in SecureSpecCombinator)
        if self.0 == v {
            Ok(Seq::empty())
        } else {
            Err(())
        }
    }
}

impl<V: View<V = V> + Eq> SecureSpecCombinator for Const<V> {
    open spec fn spec_is_prefix_secure() -> bool {
        true
    }
    
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {}

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        assert(buf.subrange(0, 0) =~= seq![]);
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {}
}

impl<V: Copy + View<V = V> + Eq> Combinator for Const<V> {
    type Result<'a> = V;
    type Owned = V;

    open spec fn spec_length(&self) -> Option<usize> {
        Some(0)
    }

    fn length(&self) -> Option<usize> {
        Some(0)
    }

    fn exec_is_prefix_secure() -> bool {
        true
    }

    open spec fn parse_requires(&self) -> bool {
        self.0.view() == self.0
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ()>) {
        Ok((0, self.0))
    }

    open spec fn serialize_requires(&self) -> bool {
        self.0.view() == self.0
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, ()>) {
        if pos < data.len() && eq(&self.0, &v) {
            assert(data@ =~= seq_splice(data@, pos, seq![]));
            Ok(0)
        } else {
            Err(())
        }
    }
}

}
