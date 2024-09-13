use vstd::prelude::*;
use super::bounds::*;

verus! {

/// Splits a byte sequence into consecutive subsequences
/// each with all non-last byte having the highest bit set
pub struct Arcs;

impl Arcs {
    pub open spec fn is_arc(&self, s: Seq<u8>) -> bool
    {
        &&& s.len() > 0
        &&& !is_high_8_bit_set!(s.last())
        &&& forall |i| 0 <= i < s.len() - 1 ==> is_high_8_bit_set!(s.index(i))
    }

    /// Defines the length of the last arc chunk
    pub open spec fn is_last_arc_chunk(&self, s: Seq<u8>, len: int) -> bool
    {
        let prev = s.len() - len - 1;

        &&& 0 < len <= s.len()
        // The suffix is the longest arc possible
        &&& s.len() == len || !is_high_8_bit_set!(s.index(prev))
        &&& self.is_arc(s.subrange(s.len() - len, s.len() as int))
    }

    proof fn lemma_is_last_arc_chunk_unique(&self, s: Seq<u8>)
        ensures
            forall |len1, len2|
                self.is_last_arc_chunk(s, len1) &&
                self.is_last_arc_chunk(s, len2) ==>
                len1 == len2
    {
        assert forall |len1, len2|
            self.is_last_arc_chunk(s, len1) &&
            self.is_last_arc_chunk(s, len2) &&
            len1 <= len2
        implies
            len1 == len2
        by {
            if len1 < len2 {
                // By contradiction
                let prev = s.len() - len1 - 1;
                let prev_in_arc2 = prev - (s.len() - len2);
                let arc2 = s.subrange(s.len() - len2, s.len() as int);

                // s.index(prev) = arc2.index(prev_in_arc2)
                assert(!is_high_8_bit_set!(s.index(prev)));
                assert(is_high_8_bit_set!(arc2.index(prev_in_arc2)));
            }
        }
    }

    pub open spec fn spec_parse(&self, s: Seq<u8>) -> Option<Seq<Seq<u8>>>
        decreases s.len()
    {
        if s.len() == 0 {
            Some(seq![])
        } else if exists |len| self.is_last_arc_chunk(s, len) {
            // Remove the last chunk, then continue parsing the prefix
            // Defined this way to line up with the imperative code
            let len = choose |len| self.is_last_arc_chunk(s, len);
            let arc = s.subrange(s.len() - len, s.len() as int);

            match self.spec_parse(s.take(s.len() - len)) {
                Some(arcs) => Some(arcs + seq![arc]),
                None => None
            }
        } else {
            None
        }
    }

    /// Check if all subsequences are arcs, then concatenate them
    pub open spec fn spec_serialize(&self, arcs: Seq<Seq<u8>>) -> Option<Seq<u8>>
    {
        if forall |i| 0 <= i < arcs.len() ==> #[trigger] self.is_arc(arcs[i]) {
            Some(arcs.flatten_alt())
        } else {
            None
        }
    }

    pub proof fn spec_parse_serialize_roundtrip(&self, s: Seq<u8>)
        ensures
            self.spec_parse(s) matches Some(arcs) ==> {
                &&& self.spec_serialize(arcs) is Some
                &&& self.spec_serialize(arcs) matches Some(s2) ==> s2 =~= s
            }
        
        decreases s.len()
    {
        if s.len() != 0 {
            if let Some(arcs) = self.spec_parse(s) {
                if exists |len| self.is_last_arc_chunk(s, len) {
                    let len = choose |len| self.is_last_arc_chunk(s, len);
                    let arc = s.subrange(s.len() - len, s.len() as int);
                    let prefix = s.take(s.len() - len);

                    self.spec_parse_serialize_roundtrip(prefix);

                    if let Some(prefix_arcs) = self.spec_parse(prefix) {
                        // Only some seq facts are required
                        assert((prefix_arcs + seq![arc]).drop_last() == prefix_arcs);
                    }
                }
            }
        }
    }

    pub proof fn spec_serialize_parse_roundtrip(&self, arcs: Seq<Seq<u8>>)
        ensures
            self.spec_serialize(arcs) matches Some(s) ==> {
                &&& self.spec_parse(s) is Some
                &&& self.spec_parse(s) matches Some(arcs2) ==> arcs2 =~~= arcs
            }

        decreases arcs.len()
    {
        if arcs.len() != 0 {
            if let Some(s) = self.spec_serialize(arcs) {
                let prefix_arcs = arcs.drop_last();

                self.spec_serialize_parse_roundtrip(prefix_arcs);

                let prefix = self.spec_serialize(prefix_arcs).unwrap();
                let last = arcs.last();

                assert(prefix =~= s.take(s.len() - last.len()));

                assert(self.is_last_arc_chunk(s, last.len() as int)) by {
                    assert(s.subrange(s.len() - last.len(), s.len() as int) == last);
                }

                assert(exists |len| self.is_last_arc_chunk(s, len));

                self.lemma_is_last_arc_chunk_unique(s);
            }
        }
    }
}

}
