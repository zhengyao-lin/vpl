use vstd::prelude::*;
use crate::vest::*;

verus! {

/// Combinator for variable-length integers in big-endian
/// The length is assumed to be <= var_uint_size!()

/// NOTE: the proofs below should be independent of the choice of VarUIntResult here
pub type VarUIntResult = u64;

/// Using macro so that it can be used in bit_vector proofs
#[allow(unused_macros)]
macro_rules! var_uint_size {
    () => { 8 };
}

#[allow(unused_macros)]
macro_rules! n_byte_max {
    ($n:expr) => { VarUIntResult::MAX >> (8 * (var_uint_size!() - $n) as usize) }
}

#[allow(unused_macros)]
macro_rules! fits_n_bytes {
    ($v:expr, $n:expr) => {
        $v <= n_byte_max!($n)
    };
}

pub struct VarUInt(pub usize);

impl View for VarUInt {
    type V = VarUInt;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl VarUInt {
    pub open spec fn wf(&self) -> bool
    {
        self.0 <= var_uint_size!()
    }

    pub open spec fn in_bound(&self, v: VarUIntResult) -> bool
    {
        fits_n_bytes!(v, self.0)
    }
}

impl SpecCombinator for VarUInt {
    type SpecResult = VarUIntResult;

    /// Parse the first `self.0` bytes of `s` as an unsigned integer in big-endian
    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, VarUIntResult), ()>
        decreases self.0
    {
        if !self.wf() || self.0 > s.len() {
            Err(())
        } else if self.0 == 0 {
            Ok((0, 0))
        } else {
            let offset = 8 * (self.0 - 1);

            match Self((self.0 - 1) as usize).spec_parse(s.drop_first()) {
                Err(..) => Err(()),
                Ok((_, rest)) => Ok((self.0, (rest + ((s[0] as VarUIntResult) << offset)) as VarUIntResult)),
            }
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {}

    /// Serialize `v` as a big-endian integer with `self.0` bytes
    open spec fn spec_serialize(&self, v: VarUIntResult) -> Result<Seq<u8>, ()>
        decreases self.0
    {
        if !self.wf() || !self.in_bound(v) {
            Err(())
        } else if self.0 == 0 {
            Ok(seq![])
        } else {
            // Encode the least significant (self.0 - 1) bytes of v
            let offset = 8 * (self.0 - 1);
            let byte = v & ((0xff as VarUIntResult) << offset);

            match Self((self.0 - 1) as usize).spec_serialize((v - byte) as VarUIntResult) {
                Err(..) => Err(()),
                Ok(rest) => Ok(seq![ (v >> offset) as u8 ] + rest),
            }
        }
    }
}

/// Some lemmas about VarUInt::spec_parse and VarUInt::spec_serialize
impl VarUInt {
    proof fn lemma_parse_ok(&self, s: Seq<u8>)
        ensures self.spec_parse(s).is_ok() <==> self.wf() && self.0 <= s.len()
        decreases self.0
    {
        if self.0 > 0 {
            Self((self.0 - 1) as usize).lemma_parse_ok(s.drop_first());
        }
    }

    proof fn lemma_parse_ok_bound(&self, s: Seq<u8>)
        requires self.spec_parse(s).is_ok()
        ensures self.in_bound(self.spec_parse(s).unwrap().1)
        decreases self.0
    {
        if self.0 > 0 {
            let rest = Self((self.0 - 1) as usize);
            
            rest.lemma_parse_ok_bound(s.drop_first());

            let s_0 = s[0];
            let (_, rest_parsed) = rest.spec_parse(s.drop_first()).unwrap();
            let self_len = self.0;

            // If rest_parsed is in_bound (wrt self.0 - 1)
            // so does rest_parsed + (s_0 << 8 * (self_len - 1)) (wrt self.0)
            assert(
                0 < self_len <= 8 ==>
                fits_n_bytes!(rest_parsed, self_len - 1) ==>
                fits_n_bytes!(
                    rest_parsed + ((s_0 as VarUIntResult) << 8 * ((self_len - 1) as usize)),
                    self_len
                )
            ) by (bit_vector);
        }
    }

    proof fn lemma_serialize_ok(&self, v: VarUIntResult)
        ensures self.spec_serialize(v).is_ok() <==> self.wf() && self.in_bound(v)
        decreases self.0
    {
        if 0 < self.0 <= var_uint_size!() && self.in_bound(v) {
            let self_len = self.0;

            let offset = 8 * (self.0 - 1);
            let byte = v & ((0xff as VarUIntResult) << offset);
            let rest = Self((self.0 - 1) as usize);

            rest.lemma_serialize_ok((v - byte) as VarUIntResult);

            assert(self.spec_serialize(v).is_ok() <==> rest.spec_serialize((v - byte) as VarUIntResult).is_ok());

            // Essentially saying self.in_bound(v) iff rest.in_bound(v - byte) but purely in BV
            assert(
                0 < self_len <= var_uint_size!() ==>
                (
                    fits_n_bytes!(v, self_len) <==>
                    fits_n_bytes!(
                        (v - (v & ((0xff as VarUIntResult) << 8 * ((self_len - 1) as VarUIntResult)))),
                        self_len - 1
                    )
                )
            ) by (bit_vector);
        }
    }

    proof fn lemma_serialize_ok_len(&self, v: VarUIntResult)
        requires self.spec_serialize(v).is_ok()
        ensures self.spec_serialize(v).unwrap().len() == self.0
        decreases self.0
    {
        if self.0 > 0 {
            let offset = 8 * (self.0 - 1);
            let byte = v & ((0xff as VarUIntResult) << offset);
            let rest = Self((self.0 - 1) as usize);
            rest.lemma_serialize_ok_len((v - byte) as VarUIntResult);
        }
    }
}

impl SecureSpecCombinator for VarUInt {
    open spec fn spec_is_prefix_secure() -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: VarUIntResult)
        decreases self.0
    {
        if self.in_bound(v) {
            if 0 < self.0 <= var_uint_size!() {
                let offset = 8 * (self.0 - 1);
                let byte = v & ((0xff as VarUIntResult) << offset);
                let rest = Self((self.0 - 1) as usize);

                rest.theorem_serialize_parse_roundtrip((v - byte) as VarUIntResult);

                self.lemma_serialize_ok(v);
                self.lemma_serialize_ok_len(v);

                let b = self.spec_serialize(v).unwrap();
                self.lemma_parse_ok(b);

                let (len, v2) = self.spec_parse(b).unwrap();

                // By definition of spec_parse
                assert(v2 ==
                    (rest.spec_parse(b.drop_first()).unwrap().1 +
                    ((b[0] as VarUIntResult) << offset)) as VarUIntResult);

                // By definition of spec_serialize
                assert(b[0] == (v >> offset) as u8);
                assert(b.drop_first() == rest.spec_serialize((v - byte) as VarUIntResult).unwrap());
                
                // Expand out everything purely in BV
                // NOTE: this depends on the size of VarUIntResult
                let self_len = self.0;
                assert(
                    0 < self_len <= var_uint_size!() ==>
                    v == (
                        // (v - byte) as VarUIntResult
                        (v - (v & ((0xff as VarUIntResult) << 8 * ((self_len - 1) as VarUIntResult)))) as VarUIntResult +

                        // (b[0] as VarUIntResult) << offset
                        (((v >> 8 * ((self_len - 1) as VarUIntResult)) as u8 as VarUIntResult) << 8 * ((self_len - 1) as VarUIntResult))
                    ) as VarUIntResult
                ) by (bit_vector);
            } else if self.0 == 0 {
                assert(n_byte_max!(0) == 0) by (bit_vector);
            }
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
        decreases self.0
    {
        if 0 < self.0 <= var_uint_size!() && self.0 <= buf.len() {
            self.lemma_parse_ok(buf);
            self.lemma_parse_ok_bound(buf);

            let (len, v) = self.spec_parse(buf).unwrap();
            self.lemma_serialize_ok(v);
            self.lemma_serialize_ok_len(v);

            let buf2 = self.spec_serialize(v).unwrap();

            assert(buf2.len() == len);

            let offset = 8 * (self.0 - 1);
            let byte = v & ((0xff as VarUIntResult) << offset);
            let rest = Self((self.0 - 1) as usize);
            let (_, rest_parsed) = rest.spec_parse(buf.drop_first()).unwrap();

            rest.theorem_parse_serialize_roundtrip(buf.drop_first());

            rest.lemma_parse_ok(buf.drop_first());

            let self_len = self.0;
            let buf_0 = buf[0];
            let buf2_0 = buf2[0];

            // First prove that buf2[0] == buf[0]
            assert(buf2[0] == buf[0]) by {
                // By definition of spec_parse
                // (rest_parsed + (buf_0 << 8 * (len - 1))) >> 8 * (len - 1) == buf_0
                assert(
                    0 < self_len <= var_uint_size!() ==>
                    fits_n_bytes!(rest_parsed, self_len - 1) ==>
                    (((rest_parsed + ((buf_0 as VarUIntResult) << 8 * ((self_len - 1) as usize))) as VarUIntResult) >> 8 * ((self_len - 1) as usize)) as u8 == buf_0
                ) by (bit_vector);
            }

            // Then prove that the rest of buf2 and buf are the same
            assert((rest_parsed + ((buf[0] as VarUIntResult) << offset)) as VarUIntResult == v);

            assert(rest_parsed == (v - ((buf[0] as VarUIntResult) << offset)) as VarUIntResult) by {
                assert(
                    0 < self_len <= 8 ==>
                    (rest_parsed + ((buf_0 as VarUIntResult) << 8 * ((self_len - 1) as usize))) as VarUIntResult == v ==>
                    rest_parsed == (v - ((buf_0 as VarUIntResult) << 8 * ((self_len - 1) as usize))) as VarUIntResult
                ) by (bit_vector);
            }
            assert(v & ((0xff as VarUIntResult) << offset) == ((buf[0] as VarUIntResult) << offset)) by {
                assert(
                    0 < self_len <= 8 ==>
                    v == (rest_parsed + ((buf_0 as VarUIntResult) << 8 * ((self_len - 1) as usize))) as VarUIntResult ==>
                    fits_n_bytes!(rest_parsed, self_len - 1) ==>
                    v & ((0xff as VarUIntResult) << 8 * ((self_len - 1) as usize)) == ((buf_0 as VarUIntResult) << 8 * ((self_len - 1) as usize))
                ) by (bit_vector);
            }

            assert(buf2.drop_first() =~= buf.subrange(0, len as int).drop_first());

            // Then we can conclude that buf2 == buf[0..len]
            assert(buf2 =~= buf.subrange(0, len as int));
        } else if self.0 == 0 {
            assert(n_byte_max!(0) == 0) by (bit_vector);
            assert(buf.subrange(0, 0) =~= seq![]);
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
        decreases self.0
    {
        if 0 < self.0 <= s1.len() && self.spec_parse(s1).is_ok() {
            Self((self.0 - 1) as usize).lemma_prefix_secure(s1.drop_first(), s2);
            assert(s1.drop_first().add(s2) =~= s1.add(s2).drop_first());
        }
    }
}

impl Combinator for VarUInt {
    type Result<'a> = VarUIntResult;
    type Owned = VarUIntResult;

    open spec fn spec_length(&self) -> Option<usize> {
        Some(self.0)
    }

    fn length(&self) -> Option<usize> {
        Some(self.0)
    }

    fn exec_is_prefix_secure() -> bool {
        true
    }

    open spec fn parse_requires(&self) -> bool {
        self.0 <= var_uint_size!()
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ()>) {
        if self.0 > s.len() {
            return Err(());
        }

        proof {
            self.lemma_parse_ok(s@);
        }

        let len = self.0;
        let mut res = 0;
        let mut i = len;

        // TODO: Unroll this for better performance?
        while i > 0
            invariant
                0 <= i <= len,
                len <= var_uint_size!(),
                len <= s.len(),

                fits_n_bytes!(res, (var_uint_size!() - i)),
                
                // At each iteration, res is the parse result of a suffix of s
                res == Self((len - i) as usize).spec_parse(s@.skip(i as int)).unwrap().1,
        {
            let byte = s[i - 1];
            
            // Prove some bounds for ruling out arithmetic overflow
            assert(
                // Some context not captured by BV solver
                0 < i <= len ==>
                len <= var_uint_size!() ==>
                fits_n_bytes!(res, (var_uint_size!() - i)) ==>
                {
                    &&& fits_n_bytes!(
                        res + ((byte as VarUIntResult) << (8 * (len - i) as usize)),
                        (var_uint_size!() - (i - 1))
                    )

                    // Shows no overflow for the the current iteration
                    // TODO: this is dependent on the size of VarUIntResult
                    &&& n_byte_max!(var_uint_size!() - i) <= 0x00ff_ffff_ffff_ffffu64
                    &&& ((byte as VarUIntResult) << (8 * (len - i) as usize)) <= 0xff00_0000_0000_0000u64
                }
            ) by (bit_vector);

            let ghost old_res = res;
            let ghost old_i = i;

            res = res + ((byte as VarUIntResult) << 8 * (len - i));
            i = i - 1;

            proof {
                let suffix = s@.skip(i as int);
                assert(suffix.drop_first() =~= s@.skip(old_i as int));
                Self((len - i) as usize).lemma_parse_ok(suffix);
                Self((len - old_i) as usize).lemma_parse_ok(suffix.drop_first());
            }
        }

        assert(s@ == s@.skip(0));
        Ok((len, res))
    }

    open spec fn serialize_requires(&self) -> bool {
        self.0 <= var_uint_size!()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, ()>) {
        assume(false);
        Err(())
    }
}

}
