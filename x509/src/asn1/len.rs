// Combinator for the length field in a TLV tuple

use vstd::prelude::*;
use crate::vest::*;
use crate::vint::*;

verus! {

pub struct Length;

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

pub proof fn lemma_min_num_bytes_exists_helper(v: VarUIntResult, n: usize)
    requires
        forall |n2: usize| #![auto]
            n <= n2 <= var_uint_size!() ==> fits_n_bytes!(v, n2)

    ensures exists |n2: usize| is_min_num_bytes_unsigned(v, n2)
{
    // TODO
    if n == 1 {
        assert(n <= 1 <= var_uint_size!());
        // assert(fits_n_bytes!(v, 1));
        assume(false);
    } else {
        assume(false);
    }
}

pub proof fn lemma_min_num_bytes_exists(v: VarUIntResult)
    ensures exists |n: usize| is_min_num_bytes_unsigned(v, n)
{
    assert(fits_n_bytes!(v, var_uint_size!())) by (bit_vector);
    // assert(!forall |n: usize|
    //     0 < n <= var_uint_size!() ==>
    //     !{
    //         &&& n <= var_uint_size!()
    //         &&& if v == 0 {
    //             n == 0
    //         } else {
    //             &&& n > 0
    //             &&& fits_n_bytes!(v, n)
    //             &&& !fits_n_bytes!(v, n - 1)
    //         }
    //     }
    // ) by (bit_vector);
    // assert(exists |n: usize| {
    //     &&& n <= var_uint_size!()
    //     &&& if v == 0 {
    //         n == 0
    //     } else {
    //         &&& n > 0
    //         &&& fits_n_bytes!(v, n)
    //         &&& !fits_n_bytes!(v, n - 1)
    //     }
    // }) by (bit_vector);
    assume(false);
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

// pub open spec fn min_num_bytes_unsigned(v: VarUIntResult) -> usize
// {
//     min_num_bytes_unsigned_helper(v, var_uint_size!())
// }

// pub open spec fn min_num_bytes_unsigned_helper(v: VarUIntResult, n: usize) -> usize
//     decreases n
// {
//     if n == 0 {
//         0
//     } else if !fits_n_bytes!(v, n - 1) {
//         n
//     } else {
//         min_num_bytes_unsigned_helper(v, (n - 1) as usize)
//     }
// }

// pub proof fn lemma_min_num_bytes_unsigned_bound(v: VarUIntResult)
//     requires v > 0

//     ensures
//         fits_n_bytes!(v, min_num_bytes_unsigned(v)),
//         !fits_n_bytes!(v, min_num_bytes_unsigned(v) - 1),
// {
//     // lemma_min_num_bytes_unsigned_bound_helper(v, min_num_bytes_unsigned(v));
//     assume(false);
// }

// // pub proof fn lemma_min_num_bytes_unsigned_bound_helper(v: VarUIntResult, n: usize)
// //     requires
// //         v > 0,
// //         min_num_bytes_unsigned(v) == n,

// //     ensures
// //         fits_n_bytes!(v, n),
// //         !fits_n_bytes!(v, n - 1),

// //     decreases n
// // {
// //     if n != 0 && fits_n_bytes!(v, n - 1) {
// //         lemma_min_num_bytes_unsigned_bound_helper(v, (n - 1) as usize);
// //         assume(false);
// //     }

// //     // assume(false);
// // }

// pub proof fn lemma_min_num_bytes_unsigned_non_zero(v: VarUIntResult)
//     requires v > 0
//     ensures min_num_bytes_unsigned(v) > 0
// {
//     assume(false);
// }

// /// An existential characterization of min_num_bytes_unsigned
// pub proof fn lemma_min_num_bytes_unsigned_alt(v: VarUIntResult, n: usize)
//     requires
//         n > 0,
//         fits_n_bytes!(v, n),
//         !fits_n_bytes!(v, n - 1),
    
//     ensures min_num_bytes_unsigned(v) == n
// {
//     assume(false);
// }

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
                // lemma_min_num_bytes_unsigned_bound(v);
                // lemma_min_num_bytes_unsigned_non_zero(v);
                lemma_min_num_bytes_exists(v);

                VarUInt(bytes).theorem_serialize_parse_roundtrip(v);
                VarUInt(bytes).lemma_serialize_ok_len(v);

                let buf2 = VarUInt(bytes).spec_serialize(v).unwrap();
                assert(buf.drop_first() == buf2);

                // assert(VarUInt(bytes).spec_serialize(v).is_ok());
                // assert(buf == seq![(0x80 + bytes) as u8] + buf2);

                // assert(VarUInt(bytes).spec_parse(buf2).is_ok());

                // assert((((0x80 + bytes) as u8) - 0x80) as usize == bytes);
                // assert(self.spec_parse(buf).is_ok());

                // let (len, v2) = self.spec_parse(buf).unwrap();

                // assert(v2 == VarUInt(bytes).spec_parse(buf2).unwrap().1);

                // assert(VarUInt(bytes).spec_parse(buf2).unwrap().1 == v);

                // assert(len == buf.len());
                // assert(v2 == v);

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

                assert(fits_n_bytes!(v2, bytes));
                assert(v2 > n_byte_max!(bytes - 1));
                // lemma_min_num_bytes_unsigned_alt(v2, bytes);
                assert(is_min_num_bytes_unsigned(v2, bytes));
                // lemma_min_num_bytes_exists(v2);
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

}
