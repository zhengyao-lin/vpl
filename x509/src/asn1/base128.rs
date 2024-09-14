use vstd::prelude::*;

use super::bounds::*;
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
                match self.spec_parse(s.drop_last(), false) {
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
                assert(s.drop_last() == empty);

                let last = s.last();

                assert(self.spec_parse(s.drop_last(), false).unwrap() == 0);
                assert(
                    v == 0 ==>
                    (v << 7 | take_low_7_bits!(last) as UInt) == 0 ==>
                    take_low_7_bits!(last) == 0
                ) by (bit_vector);
            } else if s.len() > 1 {
                self.lemma_spec_parse_unique_zero_encoding_alt(s.drop_last());

                let prefix = s.drop_last();
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
            let prefix = s.drop_last();
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
                let prefix = s.drop_last();
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

    pub proof fn lemma_spec_parse_is_arc(&self, s: Seq<u8>)
        requires self.spec_parse(s, true).is_some()
        ensures Arcs.is_arc(s)
    {
        assume(false);
    }

    pub proof fn lemma_spec_serialize_is_arc(&self, v: UInt)
        ensures Arcs.is_arc(self.spec_serialize(v, true))
    {
        assume(false);
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

            assert(s.drop_last() == prefix);

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

}
