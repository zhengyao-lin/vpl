use vstd::prelude::*;

use polyfill::*;

use crate::utils::*;
use crate::common::*;

use super::bounds::*;
use super::var_int::*;

verus! {

/// Combinator for the length field in a TLV tuple
#[derive(Debug)]
pub struct Length;
impl_trivial_view!(Length);

pub type LengthValue = VarUIntResult;

impl SpecCombinator for Length {
    type SpecResult = LengthValue;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()>
    {
        if s.len() == 0 {
            Err(())
        } else if s[0] < 0x80 {
            // One-byte length
            Ok((1, s[0] as LengthValue))
        } else {
            // Multi-byte length
            let bytes = (s[0] - 0x80) as UInt;
            match VarUInt(bytes as usize).spec_parse(s.drop_first()) {
                Ok((n, v)) => {
                    // Need to check for minimal encoding for non-malleability
                    // For 1-byte length, v > 0x7f
                    // For (2+)-byte length, v can not be represented by fewer bytes
                    if bytes > 0 && !fits_n_bytes_unsigned!(v, bytes - 1) && v > 0x7f {
                        Ok(((n + 1) as usize, v))
                    } else {
                        Err(())
                    }
                }
                Err(()) => Err(()),
            }
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {}

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()>
    {
        if v < 0x80 {
            Ok(seq![v as u8])
        } else {
            // Find the minimum number of bytes required to represent v
            let bytes = min_num_bytes_unsigned(v);

            match VarUInt(bytes as usize).spec_serialize(v) {
                Ok(buf) => Ok(seq![(0x80 + bytes) as u8] + buf),
                Err(()) => Err(()),
            }
        }
    }
}

impl SecureSpecCombinator for Length {
    open spec fn spec_is_prefix_secure() -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        if let Ok(buf) = self.spec_serialize(v) {
            if v >= 0x80 {
                let bytes = min_num_bytes_unsigned(v);
                let var_uint = VarUInt(bytes as usize);

                lemma_min_num_bytes_unsigned(v);

                var_uint.theorem_serialize_parse_roundtrip(v);
                var_uint.lemma_serialize_ok_len(v);

                let buf2 = var_uint.spec_serialize(v).unwrap();
                assert(buf.drop_first() == buf2);
            }
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if let Ok((n, v)) = self.spec_parse(buf) {
            if buf[0] < 0x80 {
                assert(seq![ buf[0] ] == buf.subrange(0, 1));
            } else {
                let bytes = (buf[0] - 0x80) as UInt;
                let var_uint = VarUInt(bytes as usize);

                // Base lemmas from VarUInt
                var_uint.theorem_parse_serialize_roundtrip(buf.drop_first());
                var_uint.lemma_parse_ok(buf.drop_first());
                var_uint.lemma_parse_ok_bound(buf.drop_first());

                // Parse the inner VarUInt
                let (len, v2) = var_uint.spec_parse(buf.drop_first()).unwrap();

                assert(is_min_num_bytes_unsigned(v2, bytes));
                lemma_min_num_bytes_unsigned(v2);

                // Some sequence facts
                assert(var_uint.spec_serialize(v).is_ok());
                let buf2 = var_uint.spec_serialize(v).unwrap();
                assert(seq![(0x80 + bytes) as u8] + buf2 == buf.subrange(0, 1 + bytes));
            }
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        if s1.len() > 0 {
            let bytes = (s1[0] - 0x80) as UInt;
            VarUInt(bytes as usize).lemma_prefix_secure(s1.drop_first(), s2);
            assert((s1 + s2).drop_first() =~= s1.drop_first() + s2);
        }
    }
}

impl Combinator for Length {
    type Result<'a> = LengthValue;
    type Owned = LengthValue;

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
        if s.len() == 0 {
            return Err(());
        }

        if s[0] < 0x80 {
            // One-byte length
            return Ok((1, s[0] as LengthValue));
        }

        let bytes = (s[0] - 0x80) as UInt;

        let (len, v) = VarUInt(bytes as usize).parse(slice_drop_first(s))?;

        if bytes > 0 && !fits_n_bytes_unsigned!(v, bytes - 1) && v > 0x7f {
            Ok(((len + 1) as usize, v))
        } else {
            Err(())
        }
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, ()>) {
        if v < 0x80 {
            if pos < data.len() {
                data.set(pos, v as u8);
                assert(data@ =~= seq_splice(old(data)@, pos, seq![v as u8]));
                return Ok(1);
            } else {
                return Err(());
            }
        }

        let bytes = min_num_bytes_unsigned_exec(v);

        // Check if out of bound
        if pos >= data.len() || pos > usize::MAX - 1 {
            return Err(());
        }

        data.set(pos, (0x80 + bytes) as u8);
        let len = VarUInt(bytes as usize).serialize(v, data, pos + 1)?;

        proof {
            lemma_min_num_bytes_unsigned(v);
            assert(data@ =~= seq_splice(old(data)@, pos, self@.spec_serialize(v).unwrap()));
        }

        Ok(len + 1)
    }
}

}
