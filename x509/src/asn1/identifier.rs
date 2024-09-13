use vstd::prelude::*;

use polyfill::*;

use super::bounds::*;
use super::vest::*;
use super::octet_string::*;
use super::arcs::*;
use super::base128::*;

verus! {

/// Combinator for a sequence of base 128 integers
/// (composing Base128UInt and Arcs)
pub struct ObjectIdentifierInner;

impl View for ObjectIdentifierInner {
    type V = ObjectIdentifierInner;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecCombinator for ObjectIdentifierInner {
    type SpecResult = Seq<UInt>;

    /// Composition of Base128UInt and Arcs modulo some overflow checks
    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        match Arcs.spec_parse(s) {
            Some(arcs) => {
                if forall |i| 0 <= i < arcs.len()
                    ==> #[trigger] Base128UInt.spec_parse(arcs[i], true).is_some() {
                    Ok((
                        s.len() as usize,
                        Seq::new(arcs.len(), |i: int| Base128UInt.spec_parse(arcs[i], true).unwrap())
                    ))
                } else {
                    Err(())
                }
            }
            None => Err(())
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {}

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        let arcs = Seq::new(
            v.len(),
            |i: int| Base128UInt.spec_serialize(v.index(i), true)
        );
        match Arcs.spec_serialize(arcs) {
            Some(s) => Ok(s),
            None => Err(()),
        }
    }
}

impl SecureSpecCombinator for ObjectIdentifierInner {
    open spec fn spec_is_prefix_secure() -> bool {
        // If another valid arc is appended, then the parsing result would be different
        false
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        if let Ok(s) = self.spec_serialize(v) {
            // Introduce some auto lemmas
            assert forall |v: UInt| true implies
                Base128UInt.spec_parse(#[trigger] Base128UInt.spec_serialize(v, true), true) == Some(v)
            by {
                Base128UInt.spec_serialize_parse_roundtrip(v, true);
            }

            assert forall |arcs: Seq<Seq<u8>>| true implies
                #[trigger] Arcs.spec_serialize(arcs) matches Some(s) ==> {
                    &&& Arcs.spec_parse(s) is Some
                    &&& Arcs.spec_parse(s) matches Some(arcs2) ==> arcs2 =~~= arcs
                }
            by {
                Arcs.spec_serialize_parse_roundtrip(arcs);
            }

            assert(self.spec_parse(s).unwrap().1 =~= v);
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if let Ok((n, v)) = self.spec_parse(buf) {
            // Introduce some auto lemmas
            assert forall |s: Seq<u8>| true implies
                #[trigger] Base128UInt.spec_parse(s, true) matches Some(v) ==>
                Base128UInt.spec_serialize(v, true) == s
            by {
                Base128UInt.spec_parse_serialize_roundtrip(s, true);
            }

            assert forall |s: Seq<u8>| true implies
                #[trigger] Arcs.spec_parse(s) matches Some(arcs) ==> {
                    &&& Arcs.spec_serialize(arcs) is Some
                    &&& Arcs.spec_serialize(arcs) matches Some(s2) ==> s2 =~= s
                }
            by {
                Arcs.spec_parse_serialize_roundtrip(s);
            }

            assert forall |v: UInt| true implies
                Arcs.is_arc(#[trigger] Base128UInt.spec_serialize(v, true))
            by {
                Base128UInt.lemma_spec_serialize_is_arc(v);
            }

            // The intermediate stage is the same
            let arcs = Arcs.spec_parse(buf).unwrap();
            let arcs2 = Seq::new(
                v.len(),
                |i: int| Base128UInt.spec_serialize(v.index(i), true)
            );
            assert(arcs =~= arcs2);

            assert(forall |i| 0 <= i < arcs.len() ==> #[trigger] Arcs.is_arc(arcs[i]));

            if let Some(buf2) = Arcs.spec_serialize(arcs2) {
                assert(buf2 =~= buf.subrange(0, n as int));
            }
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {}
}

}
