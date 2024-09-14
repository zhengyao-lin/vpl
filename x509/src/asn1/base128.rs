use vstd::prelude::*;

use super::bounds::*;
use super::vest::*;
use super::arcs::*;

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

impl View for Base128UInt {
    type V = Base128UInt;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecCombinator for Base128UInt {
    type SpecResult = UInt;

    /// A wrapper around the *_helper version but first find the length of the first arc
    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()>
    {
        match Self::find_first_arc(s) {
            Some(len) => {
                match Self::spec_parse_helper(s.take(len), true) {
                    Some(v) => Ok((len as usize, v)),
                    None => Err(())
                }
            }
            None => Err(())
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        Self::lemma_find_first_arc_alt(s);
    }

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        Ok(Self::spec_serialize_helper(v, true))
    }
}

impl SecureSpecCombinator for Base128UInt {
    open spec fn spec_is_prefix_secure() -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        Self::lemma_spec_serialize_find_first_arc(v);
        Self::spec_serialize_parse_helper_roundtrip(v, true);

        let s = Self::spec_serialize_helper(v, true);
        assert(s.take(s.len() as int) == s);
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if let Some(len) = Self::find_first_arc(buf) {
            Self::lemma_find_first_arc_alt(buf);
            self.lemma_prefix_secure(buf.take(len), buf.skip(len));
            Self::spec_parse_serialize_helper_roundtrip(buf.take(len), true);

            assert(buf.take(len) + buf.skip(len) == buf);
            assert(buf.take(len) == buf.subrange(0, len));
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        Self::lemma_find_first_arc_alt(s1);
        Self::lemma_find_first_arc_prefix_secure(s1, s2);

        if let Some(len) = Self::find_first_arc(s1) {
            assert(s1.take(len) == (s1 + s2).take(len));
        }
    }
}

impl Base128UInt {
    /// last_byte is true iff s includes the last byte (which much exists and have the highest bit set to 0)
    pub open spec fn spec_parse_helper(s: Seq<u8>, last_byte: bool) -> Option<UInt>
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
                match Self::spec_parse_helper(s.drop_last(), false) {
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
    pub open spec fn spec_serialize_helper(v: UInt, last_byte: bool) -> Seq<u8>
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
            Self::spec_serialize_helper(v >> 7, false) + seq![take_low_7_bits!(v)]
        } else {
            // Add the lowest 7 bits with the highest bit set to 0
            Self::spec_serialize_helper(v >> 7, false) + seq![set_high_8_bit!(v)]
        }
    }

    pub open spec fn find_first_arc(s: Seq<u8>) -> Option<int>
        decreases s.len()
    {
        if s.len() == 0 {
            None
        } else {
            if !is_high_8_bit_set!(s.first()) {
                Some(1)
            } else {
                match Self::find_first_arc(s.drop_first()) {
                    Some(len) => Some(len + 1),
                    None => None
                }
            }
        }
    }

    /// A spec fn wrapper of the macro for quantifier triggers
    closed spec fn is_high_8_bit_set(v: u8) -> bool
    {
        is_high_8_bit_set!(v)
    }

    closed spec fn all_high_8_bit_set(s: Seq<u8>) -> bool
    {
        forall |i: int| 0 <= i < s.len() ==> #[trigger] Self::is_high_8_bit_set(s.index(i))
    }

    /// An alternative characterization of find_first_arc
    proof fn lemma_find_first_arc_alt(s: Seq<u8>)
        ensures
            Self::find_first_arc(s) matches Some(len) ==> {
                let last = s[len - 1];

                &&& 0 < len <= s.len()
                &&& !Self::is_high_8_bit_set(last)
                &&& Self::all_high_8_bit_set(s.take(len - 1))
            },
            Self::find_first_arc(s) is None ==> Self::all_high_8_bit_set(s),

        decreases s.len()
    {
        if s.len() != 0 {
            if is_high_8_bit_set!(s.first()) {
                Self::lemma_find_first_arc_alt(s.drop_first());

                if let Some(len) = Self::find_first_arc(s.drop_first()) {
                    assert(0 < len <= s.drop_first().len());

                    let last = s[len];
                    assert(last == s.drop_first()[len - 1]);
                    
                    assert forall |i: int| 0 <= i < len implies #[trigger] Self::is_high_8_bit_set(s.index(i))
                    by {
                        if i > 0 {
                            assert(s.index(i) == s.drop_first().take(len - 1).index(i - 1));
                        }
                    }
                } else {
                    assert forall |i: int| 0 <= i < s.len() implies #[trigger] Self::is_high_8_bit_set(s.index(i))
                    by {
                        if i > 0 {
                            assert(s.index(i) == s.drop_first().index(i - 1));
                        }
                    }
                }
            }
        }
    }

    proof fn lemma_find_first_arc_prefix_secure(s1: Seq<u8>, s2: Seq<u8>)
        ensures
            Self::find_first_arc(s1) matches Some(len) ==>
                Self::find_first_arc(s1 + s2) == Some(len)
    
        decreases s1.len()
    {
        if s1.len() != 0 {
            Self::lemma_find_first_arc_prefix_secure(s1.drop_first(), s2);
            assert(s1.drop_first() + s2 == (s1 + s2).drop_first());
        }
    }

    proof fn lemma_spec_serialize_non_last_byte_all_high_8_bit_set(v: UInt)
        ensures
            Self::all_high_8_bit_set(Self::spec_serialize_helper(v, false))

        decreases v
    {
        if v != 0 {
            assert(v != 0 ==> v >> 7 < v) by (bit_vector);
            assert(is_high_8_bit_set!(set_high_8_bit!(v))) by (bit_vector);
            Self::lemma_spec_serialize_non_last_byte_all_high_8_bit_set(v >> 7);
        }
    }

    proof fn lemma_spec_serialize_find_first_arc(v: UInt)
        ensures
            ({
                let s = Self::spec_serialize_helper(v, true);
                Self::find_first_arc(s) == Some(s.len() as int)
            })
    {
        let s = Self::spec_serialize_helper(v, true);
        Self::lemma_spec_serialize_non_last_byte_all_high_8_bit_set(v >> 7);
        Self::lemma_find_first_arc_alt(s);

        assert(!is_high_8_bit_set!(take_low_7_bits!(v))) by (bit_vector);

        if Self::find_first_arc(s).is_none() {
            assert(Self::is_high_8_bit_set(s.last()));
        }
    }

    /// Same as lemma_spec_parse_unique_zero_encoding, but for last_byte = false
    proof fn lemma_spec_parse_unique_zero_encoding_alt(s: Seq<u8>)
        ensures Self::spec_parse_helper(s, false) matches Some(v) ==>
            (v == 0 <==> s.len() == 0)

        decreases s.len()
    {
        if let Some(v) = Self::spec_parse_helper(s, false) {
            if s.len() == 1 {
                // Show that the only byte should not be a zero

                let empty: Seq<u8> = seq![];
                assert(s.drop_last() == empty);

                let last = s.last();

                assert(Self::spec_parse_helper(s.drop_last(), false).unwrap() == 0);
                assert(
                    v == 0 ==>
                    (v << 7 | take_low_7_bits!(last) as UInt) == 0 ==>
                    take_low_7_bits!(last) == 0
                ) by (bit_vector);
            } else if s.len() > 1 {
                Self::lemma_spec_parse_unique_zero_encoding_alt(s.drop_last());

                let prefix = s.drop_last();
                let last = s.last();
                let parsed_prefix = Self::spec_parse_helper(prefix, false).unwrap();
                
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
    proof fn spec_serialize_dereases(v: UInt, last_byte: bool)
    {
        assert(v != 0 ==> v >> 7 < v) by (bit_vector);
    }

    /// The encoding of 0 is unique
    proof fn lemma_spec_parse_unique_zero_encoding(s: Seq<u8>)
        ensures
            Self::spec_parse_helper(s, true) matches Some(v) ==>
            (v == 0 <==> s =~= seq![0u8])

        decreases s.len()
    {
        // reveal_with_fuel(Self::spec_parse, 2);

        if let Some(v) = Self::spec_parse_helper(s, true) {
            let prefix = s.drop_last();
            let last = s.last();
            let parsed_prefix = Self::spec_parse_helper(prefix, false).unwrap();

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
                    Self::lemma_spec_parse_unique_zero_encoding_alt(prefix);
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

                Self::lemma_spec_parse_unique_zero_encoding(prefix);
            }
        }
    }

    // Serializing a non-zero value should not have a non-zero first byte
    proof fn lemma_spec_serialize_non_zero(v: UInt)
        requires v != 0
        ensures
            Self::spec_serialize_helper(v, false).len() > 0,
            take_low_7_bits!(Self::spec_serialize_helper(v, false).first()) != 0,
        
        decreases v
    {
        assert(
            v != 0 ==>
            take_low_7_bits!(v) != 0 ||
            v >> 7 != 0
        ) by (bit_vector);

        if v >> 7 != 0 {
            assert(v != 0 ==> v >> 7 < v) by (bit_vector);
            Self::lemma_spec_serialize_non_zero(v >> 7);
        } else {
            assert(take_low_7_bits!(v) != 0 ==> take_low_7_bits!(set_high_8_bit!(v)) != 0) by (bit_vector);
            assert(Self::spec_serialize_helper(v >> 7, false).len() == 0);
        }
    }

    pub proof fn spec_parse_serialize_helper_roundtrip(s: Seq<u8>, last_byte: bool)
        ensures
            Self::spec_parse_helper(s, last_byte) matches Some(v) ==>
            Self::spec_serialize_helper(v, last_byte) == s
        
        decreases s.len()
    {
        if let Some(v) = Self::spec_parse_helper(s, last_byte) {
            if s.len() == 0 {
                let empty: Seq<u8> = seq![];
                assert(s == empty);
            } else {
                let prefix = s.drop_last();
                let last = s.last();
                let parsed_prefix = Self::spec_parse_helper(prefix, false).unwrap();
                let s2 = Self::spec_serialize_helper(v, last_byte);

                Self::spec_parse_serialize_helper_roundtrip(prefix, false);

                assert(
                    parsed_prefix <= n_bit_max_unsigned!(8 * uint_size!() - 7) ==> {
                        &&& (parsed_prefix << 7 | take_low_7_bits!(last) as UInt) >> 7 == parsed_prefix
                        &&& (!is_high_8_bit_set!(last) ==> take_low_7_bits!(parsed_prefix << 7 | take_low_7_bits!(last) as UInt) == last)
                        &&& (is_high_8_bit_set!(last) ==> set_high_8_bit!(parsed_prefix << 7 | take_low_7_bits!(last) as UInt) == last)
                    }
                ) by (bit_vector);

                Self::lemma_spec_parse_unique_zero_encoding(s);
                Self::lemma_spec_parse_unique_zero_encoding_alt(s);

                assert(s == s2);
            }
        }
    }

    pub proof fn spec_serialize_parse_helper_roundtrip(v: UInt, last_byte: bool)
        ensures
            Self::spec_parse_helper(Self::spec_serialize_helper(v, last_byte), last_byte) == Some(v)

        decreases v
    {
        if v == 0 {
            reveal_with_fuel(Base128UInt::spec_parse_helper, 2);
            Self::lemma_spec_parse_unique_zero_encoding(seq![0u8]);
        } else {
            let s = Self::spec_serialize_helper(v, last_byte);
            let prefix = Self::spec_serialize_helper(v >> 7, false);

            assert(v != 0 ==> v >> 7 < v) by (bit_vector);
            Self::spec_serialize_parse_helper_roundtrip(v >> 7, false);

            // By definition
            // assert(s == prefix + if last_byte {
            //     seq![take_low_7_bits!(v)]
            // } else {
            //     seq![set_high_8_bit!(v)]
            // });

            assert(s.drop_last() == prefix);

            // Some required BV facts
            assert(!is_high_8_bit_set!(take_low_7_bits!(v))) by (bit_vector);
            assert(is_high_8_bit_set!(set_high_8_bit!(v))) by (bit_vector);
            assert(v >> 7 <= n_bit_max_unsigned!(8 * uint_size!() - 7)) by (bit_vector);
            assert(v >> 7 << 7 | take_low_7_bits!(take_low_7_bits!(v)) as UInt == v) by (bit_vector);
            assert(v >> 7 << 7 | take_low_7_bits!(set_high_8_bit!(v)) as UInt == v) by (bit_vector);

            Self::lemma_spec_serialize_non_zero(v);
        }
    }
}

}
