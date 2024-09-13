use vstd::prelude::*;

use polyfill::*;

use super::bounds::*;
use super::vest::*;
use super::octet_string::*;

verus! {

/// Combinator for a single identifier component
/// in the OBJECT IDENTIFIER ASN.1 type (called "arc"
/// X.690)
/// 
/// Basically an Arc is encoded as a "base-128" integer
/// where the highest bit of every byte is set to 1
/// except for the last byte
/// 
/// e.g. 0b11111111 (0xff) => 0b1 * 128 + 0b01111111 => 0b10000001 0b011111111
/// 
/// NOTE: the first and second arc of an OID are encoded differently
/// than this combinator
pub struct Base128UInt;

/// Take the lowest 7 bits as an u8
#[allow(unused_macros)]
macro_rules! take_low_7_bits {
    ($v:expr) => {
        $v as u8 & 0x7f
    };
}
pub(super) use take_low_7_bits;

/// Set the highest bit to 1 as an u8
#[allow(unused_macros)]
macro_rules! set_high_8_bit {
    ($v:expr) => {
        ($v | 0x80) as u8
    };
}
pub(super) use set_high_8_bit;

/// Check if the highest bit is set in an u8
#[allow(unused_macros)]
macro_rules! is_high_8_bit_set {
    ($v:expr) => {
        $v as u8 >= 0x80
    };
}
pub(super) use is_high_8_bit_set;

impl Base128UInt {
    /// last_byte is true iff s includes the last byte (which much exists and have the highest bit set to 0)
    pub open spec fn spec_parse(&self, s: Seq<u8>, last_byte: bool) -> Option<UInt>
        decreases s.len()
    {
        if s.len() == 0 {
            if last_byte {
                None
            } else {
                Some(0)
            }
        } else {
            if !last_byte && take_low_7_bits!(s.first()) == 0 {
                // The first byte (if not the last byte) should not be 0 for minimal encoding
                None
            } else if !last_byte && !is_high_8_bit_set!(s.last()) {
                // If s should not include the last byte, then all bytes must have the highest bit set to 1
                None
            } else if last_byte && is_high_8_bit_set!(s.last()) {
                // If s include the last byte, the last byte should have the highest bit unset
                None
            } else {
                // Parse the prefix first
                match self.spec_parse(s.take(s.len() - 1), false) {
                    Some(v) =>
                        // Check for overflow
                        if v <= n_bit_max_unsigned!(8 * uint_size!() - 7) {
                            // Remove the highest bit of s.last() when parsing
                            Some(v << 7 | take_low_7_bits!(s.last()) as UInt)
                        } else {
                            None
                        }
                    None => None
                }
            }
        }
    }

    /// Serialize v in base-128 encoding
    /// last_byte is true iff the encoding should have the highest bit of the last byte set to 0
    pub open spec fn spec_serialize(&self, v: UInt, last_byte: bool) -> Seq<u8>
        decreases v via Self::spec_serialize_dereases
    {
        if v == 0 {
            if last_byte {
                seq![0]
            } else {
                seq![]
            }
        } else if last_byte {
            // Add the lowest 7 bits of v along with the highest bit set to 1
            self.spec_serialize(v >> 7, false) + seq![take_low_7_bits!(v)]
        } else {
            // Add the lowest 7 bits with the highest bit set to 0
            self.spec_serialize(v >> 7, false) + seq![set_high_8_bit!(v)]
        }
    }

    /// Same as lemma_spec_parse_unique_zero_encoding, but for last_byte = false
    proof fn lemma_spec_parse_unique_zero_encoding_alt(&self, s: Seq<u8>)
        ensures self.spec_parse(s, false) matches Some(v) ==>
            (v == 0 <==> s.len() == 0)

        decreases s.len()
    {
        if let Some(v) = self.spec_parse(s, false) {
            if s.len() == 1 {
                // Show that the only byte should not be a zero

                let empty: Seq<u8> = seq![];
                assert(s.take(s.len() - 1) == empty);

                let last = s.last();

                assert(self.spec_parse(s.take(s.len() - 1), false).unwrap() == 0);
                assert(
                    v == 0 ==>
                    (v << 7 | take_low_7_bits!(last) as UInt) == 0 ==>
                    take_low_7_bits!(last) == 0
                ) by (bit_vector);
            } else if s.len() > 1 {
                self.lemma_spec_parse_unique_zero_encoding_alt(s.take(s.len() - 1));

                let prefix = s.take(s.len() - 1);
                let last = s.last();
                let parsed_prefix = self.spec_parse(prefix, false).unwrap();
                
                // Since prefix is not zero, neither is the final value
                assert(
                    parsed_prefix <= n_bit_max_unsigned!(8 * uint_size!() - 7) ==>
                    parsed_prefix != 0 ==>
                    parsed_prefix << 7 | take_low_7_bits!(last) as UInt != 0
                ) by (bit_vector);
            }
        }
    }

    #[via_fn]
    proof fn spec_serialize_dereases(&self, v: UInt, last_byte: bool)
    {
        assert(v != 0 ==> v >> 7 < v) by (bit_vector);
    }

    /// The encoding of 0 is unique
    proof fn lemma_spec_parse_unique_zero_encoding(&self, s: Seq<u8>)
        ensures
            self.spec_parse(s, true) matches Some(v) ==>
            (v == 0 <==> s =~= seq![0u8])

        decreases s.len()
    {
        // reveal_with_fuel(Base128UInt::spec_parse, 2);

        if let Some(v) = self.spec_parse(s, true) {
            let prefix = s.take(s.len() - 1);
            let last = s.last();
            let parsed_prefix = self.spec_parse(prefix, false).unwrap();

            assert(v == parsed_prefix << 7 | take_low_7_bits!(last) as UInt);

            if v == 0 {
                // If the concat the parsed prefix and last is 0
                // then both of them must be 0
                assert(
                    parsed_prefix <= n_bit_max_unsigned!(8 * uint_size!() - 7) ==>
                    parsed_prefix << 7 | take_low_7_bits!(last) as UInt == 0 ==>
                    !is_high_8_bit_set!(last) ==>
                    last == 0 && parsed_prefix == 0
                ) by (bit_vector);

                if prefix.len() != 0 {
                    self.lemma_spec_parse_unique_zero_encoding_alt(prefix);
                }
            } else {
                // WTS: s =~= seq![0u8]

                // If the final value is not 0,
                // then either the prefix or the last byte must not be 0
                assert(
                    parsed_prefix <= n_bit_max_unsigned!(8 * uint_size!() - 7) ==>
                    (parsed_prefix << 7 | take_low_7_bits!(last) as UInt) != 0 ==>
                    parsed_prefix != 0 || last != 0
                ) by (bit_vector);

                self.lemma_spec_parse_unique_zero_encoding(prefix);
            }
        }
    }

    // Serializing a non-zero value should not have a non-zero first byte
    proof fn lemma_spec_serialize_non_zero(&self, v: UInt)
        requires v != 0
        ensures
            self.spec_serialize(v, false).len() > 0,
            take_low_7_bits!(self.spec_serialize(v, false).first()) != 0,
        
        decreases v
    {
        assert(
            v != 0 ==>
            take_low_7_bits!(v) != 0 ||
            v >> 7 != 0
        ) by (bit_vector);

        if v >> 7 != 0 {
            assert(v != 0 ==> v >> 7 < v) by (bit_vector);
            self.lemma_spec_serialize_non_zero(v >> 7);
        } else {
            assert(take_low_7_bits!(v) != 0 ==> take_low_7_bits!(set_high_8_bit!(v)) != 0) by (bit_vector);
            assert(self.spec_serialize(v >> 7, false).len() == 0);
        }
    }

    pub proof fn spec_parse_serialize_roundtrip(&self, s: Seq<u8>, last_byte: bool)
        ensures
            self.spec_parse(s, last_byte) matches Some(v) ==>
            self.spec_serialize(v, last_byte) == s
        
        decreases s.len()
    {
        if let Some(v) = self.spec_parse(s, last_byte) {
            if s.len() == 0 {
                let empty: Seq<u8> = seq![];
                assert(s == empty);
            } else {
                let prefix = s.take(s.len() - 1);
                let last = s.last();
                let parsed_prefix = self.spec_parse(prefix, false).unwrap();
                let s2 = self.spec_serialize(v, last_byte);

                self.spec_parse_serialize_roundtrip(prefix, false);

                assert(
                    parsed_prefix <= n_bit_max_unsigned!(8 * uint_size!() - 7) ==> {
                        &&& (parsed_prefix << 7 | take_low_7_bits!(last) as UInt) >> 7 == parsed_prefix
                        &&& (!is_high_8_bit_set!(last) ==> take_low_7_bits!(parsed_prefix << 7 | take_low_7_bits!(last) as UInt) == last)
                        &&& (is_high_8_bit_set!(last) ==> set_high_8_bit!(parsed_prefix << 7 | take_low_7_bits!(last) as UInt) == last)
                    }
                ) by (bit_vector);

                self.lemma_spec_parse_unique_zero_encoding(s);
                self.lemma_spec_parse_unique_zero_encoding_alt(s);

                assert(s == s2);
            }
        }
    }

    pub proof fn spec_serialize_parse_roundtrip(&self, v: UInt, last_byte: bool)
        ensures
            self.spec_parse(self.spec_serialize(v, last_byte), last_byte) == Some(v)

        decreases v
    {
        if v == 0 {
            reveal_with_fuel(Base128UInt::spec_parse, 2);
            self.lemma_spec_parse_unique_zero_encoding(seq![0u8]);
        } else {
            let s = self.spec_serialize(v, last_byte);
            let prefix = self.spec_serialize(v >> 7, false);

            assert(v != 0 ==> v >> 7 < v) by (bit_vector);
            self.spec_serialize_parse_roundtrip(v >> 7, false);

            // By definition
            // assert(s == prefix + if last_byte {
            //     seq![take_low_7_bits!(v)]
            // } else {
            //     seq![set_high_8_bit!(v)]
            // });

            assert(s.take(s.len() - 1) == prefix);

            // Some required BV facts
            assert(!is_high_8_bit_set!(take_low_7_bits!(v))) by (bit_vector);
            assert(is_high_8_bit_set!(set_high_8_bit!(v))) by (bit_vector);
            assert(v >> 7 <= n_bit_max_unsigned!(8 * uint_size!() - 7)) by (bit_vector);
            assert(v >> 7 << 7 | take_low_7_bits!(take_low_7_bits!(v)) as UInt == v) by (bit_vector);
            assert(v >> 7 << 7 | take_low_7_bits!(set_high_8_bit!(v)) as UInt == v) by (bit_vector);

            self.lemma_spec_serialize_non_zero(v);
        }
    }
}

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

pub struct ObjectIdentifierInner;

impl View for ObjectIdentifierInner {
    type V = ObjectIdentifierInner;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

// impl SpecCombinator for ObjectIdentifierInner {
//     type SpecResult = Seq<UInt>;

//     open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
//         Err(())
//     }

//     proof fn spec_parse_wf(&self, s: Seq<u8>) {}

//     open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
//         Err(())
//     }
// }

}
