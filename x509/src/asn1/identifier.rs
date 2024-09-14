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

impl Combinator for ObjectIdentifierInner {
    type Result<'a> = &'a [UInt];
    type Owned = Vec<UInt>;

    open spec fn spec_length(&self) -> Option<usize> {
        None
    }

    fn length(&self) -> Option<usize> {
        None
    }

    fn exec_is_prefix_secure() -> bool {
        false
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ()>) {
        let mut arcs: Vec<UInt> = Vec::new();

        let mut i = 0;

        while i < s.len()
            invariant
                i > 0 ==> { let last_byte = s@[i - 1]; !is_high_8_bit_set!(last_byte) },
        {
            let j = i;
            let mut arc: UInt = 0;

            // Parse an arc from j
            while i < s.len() && is_high_8_bit_set!(s[i])
                invariant
                    0 <= j <= i <= s.len(),
                    Base128UInt.spec_parse(s@.subrange(j as int, i as int), false) =~= Some(arc),
            {
                if i == j && take_low_7_bits!(s[i]) == 0 {
                    assert(Base128UInt.spec_parse(s@.subrange(j as int, i + 1), false).is_none());
                    assert(Base128UInt.spec_parse(s@.subrange(j as int, i + 1), true).is_none());
                    assume(false);
                    return Err(());
                }

                // Check bound
                if arc > n_bit_max_unsigned!(8 * uint_size!() - 7) {
                    assert(Base128UInt.spec_parse(s@.subrange(j as int, i + 1), true).is_none());
                    assume(false);
                    return Err(());
                }

                assert(s@.subrange(j as int, i as int) =~= s@.subrange(j as int, i + 1).drop_last());
                arc = arc << 7 | take_low_7_bits!(s[i]) as UInt;
                i = i + 1;
            }
            
            if i == s.len() {
                assert(Base128UInt.spec_parse(s@.subrange(j as int, i as int), true).is_none());
                assume(false);
                return Err(());
            }
            
            // Bound check
            if arc > n_bit_max_unsigned!(8 * uint_size!() - 7) {
                assume(false);
                return Err(());
            }

            // Add the final byte
            assert(s@.subrange(j as int, i as int) =~= s@.subrange(j as int, i + 1).drop_last());
            arc = arc << 7 | take_low_7_bits!(s[i]) as UInt;
            i = i + 1;

            assert(Base128UInt.spec_parse(s@.subrange(j as int, i as int), true) =~= Some(arc));

            proof {
                Base128UInt.lemma_spec_parse_is_arc(s@.subrange(j as int, i as int));
                assert(s@.subrange(0, i as int).subrange(j as int, i as int) == s@.subrange(j as int, i as int));
                assert(Arcs.is_last_arc_chunk(s@.subrange(0, i as int), i - j));
            }

            arcs.push(arc);
        }

        assume(false);
        Err(())
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, ()>) {
        assume(false);
        Err(())
    }
}

}
