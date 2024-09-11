// Combinator for the length field in a TLV tuple

use std::f32::consts::E;

use vstd::prelude::*;
use crate::polyfill::slice_drop_first;
use crate::vest::*;
use crate::vint::*;

verus! {

pub struct Length;

impl View for Length {
    type V = Length;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

/// Minimum number of bytes required to represent an unsigned integer
/// (in an existential characterization)
pub open spec fn min_num_bytes_unsigned(v: VarUIntResult) -> usize
{
    choose |n: usize| is_min_num_bytes_unsigned(v, n)
}

pub open spec fn is_min_num_bytes_unsigned(v: VarUIntResult, n: usize) -> bool
{
    &&& n <= var_uint_size!()
    &&& if v == 0 {
        n == 0
    } else {
        &&& n > 0
        &&& fits_n_bytes!(v, n)
        &&& !fits_n_bytes!(v, n - 1)
    }
}

/// A helper induction lemma
pub proof fn lemma_well_ordering(p: spec_fn(usize) -> bool, n: usize)
    requires p(n) && !p(0)
    ensures exists |i: usize| 0 < i <= n && (#[trigger] p(i)) && !p((i - 1) as usize)
    decreases n
{
    if n > 1 && p((n - 1) as usize) {
        lemma_well_ordering(p, (n - 1) as usize);
    }
}

/// min_num_bytes_unsigned exists
pub proof fn lemma_min_num_bytes_exists(v: VarUIntResult)
    ensures exists |n: usize| is_min_num_bytes_unsigned(v, n)
{
    if v == 0 {
        assert(is_min_num_bytes_unsigned(v, 0));
    } else {
        assert(v != 0 ==> !fits_n_bytes!(v, 0)) by (bit_vector);
        assert(fits_n_bytes!(v, var_uint_size!())) by (bit_vector);

        let fits_n = |n: usize| fits_n_bytes!(v, n);
        let bytes = choose |i: usize| 0 < i <= var_uint_size!() && #[trigger] fits_n(i) && !fits_n((i - 1) as usize);

        lemma_well_ordering(fits_n, var_uint_size!());
        assert(is_min_num_bytes_unsigned(v, bytes));
    }
}

/// min_num_bytes_unsigned is unique
pub proof fn lemma_min_num_bytes_unique(v: VarUIntResult)
    ensures forall |n1: usize, n2: usize|
        is_min_num_bytes_unsigned(v, n1) &&
        is_min_num_bytes_unsigned(v, n2) ==> n1 == n2
{
    assert forall |n1: usize, n2: usize|
        is_min_num_bytes_unsigned(v, n1) &&
        is_min_num_bytes_unsigned(v, n2)
    implies n1 == n2 by {
        // By contradiction: if n2 < n1 or n1 < n2, then we can derive false by BV reasoning
        assert(n2 < n1 <= var_uint_size!() ==> !(fits_n_bytes!(v, n2) && !fits_n_bytes!(v, n1 - 1))) by (bit_vector);
        assert(n1 < n2 <= var_uint_size!() ==> !(fits_n_bytes!(v, n1) && !fits_n_bytes!(v, n2 - 1))) by (bit_vector);
    };
}

/// Exec version of min_num_bytes_unsigned
pub fn min_num_bytes_unsigned_exec(v: VarUIntResult) -> (res: usize)
    ensures is_min_num_bytes_unsigned(v, res)
{
    let mut n = var_uint_size!();

    assert(n == var_uint_size!() ==> fits_n_bytes!(v, n)) by (bit_vector);

    while n > 0
        invariant
            0 <= n <= var_uint_size!(),
            fits_n_bytes!(v, n),
    {
        if !fits_n_bytes!(v, n - 1) {
            return n;
        }
        n = n - 1;
    }

    assert(fits_n_bytes!(v, 0) ==> v == 0) by (bit_vector);
    
    return 0;
}

impl SpecCombinator for Length {
    type SpecResult = VarUIntResult;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()>
    {
        if s.len() == 0 {
            Err(())
        } else if s[0] < 0x80 {
            // One-byte length
            Ok((1, s[0] as VarUIntResult))
        } else {
            // Multi-byte length
            let bytes = (s[0] - 0x80) as usize;
            match VarUInt(bytes).spec_parse(s.drop_first()) {
                Ok((n, v)) => {
                    // Need to check for minimal encoding for non-malleability
                    // For 1-byte length, v > 0x7f
                    // For (2+)-byte length, v can not be represented by fewer bytes
                    if bytes > 0 && !fits_n_bytes!(v, bytes - 1) && v > 0x7f {
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

            match VarUInt(bytes).spec_serialize(v) {
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
                lemma_min_num_bytes_exists(v);

                VarUInt(bytes).theorem_serialize_parse_roundtrip(v);
                VarUInt(bytes).lemma_serialize_ok_len(v);

                let buf2 = VarUInt(bytes).spec_serialize(v).unwrap();
                assert(buf.drop_first() == buf2);
            }
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if let Ok((n, v)) = self.spec_parse(buf) {
            if buf[0] < 0x80 {
                assert(seq![ buf[0] ] == buf.subrange(0, 1));
            } else {
                let bytes = (buf[0] - 0x80) as usize;

                // Base lemmas from VarUInt
                VarUInt(bytes).theorem_parse_serialize_roundtrip(buf.drop_first());
                VarUInt(bytes).lemma_parse_ok(buf.drop_first());
                VarUInt(bytes).lemma_parse_ok_bound(buf.drop_first());

                // Parse the inner VarUInt
                let (len, v2) = VarUInt(bytes).spec_parse(buf.drop_first()).unwrap();

                assert(is_min_num_bytes_unsigned(v2, bytes));
                lemma_min_num_bytes_unique(v2);

                // Some sequence facts
                assert(VarUInt(bytes).spec_serialize(v).is_ok());
                let buf2 = VarUInt(bytes).spec_serialize(v).unwrap();
                assert(seq![(0x80 + bytes) as u8] + buf2 == buf.subrange(0, 1 + bytes));
            }
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        if s1.len() > 0 {
            let bytes = (s1[0] - 0x80) as usize;
            VarUInt(bytes).lemma_prefix_secure(s1.drop_first(), s2);
            assert((s1 + s2).drop_first() =~= s1.drop_first() + s2);
        }
    }
}

impl Combinator for Length {
    type Result<'a> = VarUIntResult;
    type Owned = VarUIntResult;

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
            return Ok((1, s[0] as VarUIntResult));
        }

        let bytes = (s[0] - 0x80) as usize;

        let (len, v) = VarUInt(bytes).parse(slice_drop_first(s))?;

        if bytes > 0 && !fits_n_bytes!(v, bytes - 1) && v > 0x7f {
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
        let len = VarUInt(bytes).serialize(v, data, pos + 1)?;

        proof {
            lemma_min_num_bytes_unique(v);
            assert(data@ =~= seq_splice(old(data)@, pos, self@.spec_serialize(v).unwrap()));
        }

        Ok(len + 1)
    }
}

}
