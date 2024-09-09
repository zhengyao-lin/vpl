use vstd::prelude::*;
use crate::vest::*;

verus! {

/// Combinator for variable-length integers in big-endian
/// The length is assumed to be <= var_uint_size!()

/// NOTE: the proofs below should be independent of the choice of VarUIntResult.
/// To change the definition of VarUIntResult (to u128, for example)
/// we only need to change these macros
///   - var_uint_size!
///   - var_uint_max_without_first_byte!
///   - var_uint_max_first_byte!
pub type VarUIntResult = u64;

/// Using macro utils so that they can be expanded in bit_vector proofs
#[allow(unused_macros)]
macro_rules! var_uint_size {
    () => { 8 };
}

#[allow(unused_macros)]
macro_rules! var_uint_max_without_first_byte {
    () => { 0x00ff_ffff_ffff_ffffu64 };
}

#[allow(unused_macros)]
macro_rules! var_uint_max_first_byte {
    () => { 0xff00_0000_0000_0000u64 };
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

/// Get the nth-least significant byte (counting from 0)
#[allow(unused_macros)]
macro_rules! get_nth_byte {
    ($v:expr, $n:expr) => {
        ($v >> (8 * ($n as usize))) as u8
    };
}

/// Prepend $b as the $n-th byte (counting from 0) of $v
/// Assuming $v fits in $n bytes
#[allow(unused_macros)]
macro_rules! prepend_byte {
    ($v:expr, $b:expr, $n:expr) => {
        ($v + (($b as VarUIntResult) << (8 * ($n as usize)))) as VarUIntResult
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
            let byte = s[0];
            match Self((self.0 - 1) as usize).spec_parse(s.drop_first()) {
                Err(..) => Err(()),
                Ok((_, rest)) => Ok((self.0, prepend_byte!(rest, byte, self.0 - 1))),
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
            // then prepend the self.0-th byte
            match Self((self.0 - 1) as usize).spec_serialize(v & n_byte_max!(self.0 - 1)) {
                Err(..) => Err(()),
                Ok(rest) => Ok(seq![ get_nth_byte!(v, self.0 - 1) ] + rest),
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

    /// Parsed results should fit in self.0 bytes
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
            // so does prepend_byte!(rest_parsed, s_0, self_len - 1) (wrt self.0)
            assert(
                0 < self_len <= var_uint_size!() ==>
                fits_n_bytes!(rest_parsed, self_len - 1) ==>
                fits_n_bytes!(
                    prepend_byte!(rest_parsed, s_0, self_len - 1),
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
            Self((self.0 - 1) as usize).lemma_serialize_ok(v & n_byte_max!(self_len - 1));
            assert(fits_n_bytes!(v & n_byte_max!(self_len - 1), self_len - 1)) by (bit_vector);
        }
    }

    proof fn lemma_serialize_ok_len(&self, v: VarUIntResult)
        requires self.spec_serialize(v).is_ok()
        ensures self.spec_serialize(v).unwrap().len() == self.0
        decreases self.0
    {
        if self.0 > 0 {
            Self((self.0 - 1) as usize).lemma_serialize_ok_len(v & n_byte_max!(self.0 - 1));
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
                let rest = Self((self.0 - 1) as usize);

                rest.theorem_serialize_parse_roundtrip(v & n_byte_max!(self.0 - 1));

                self.lemma_serialize_ok(v);
                self.lemma_serialize_ok_len(v);

                let b = self.spec_serialize(v).unwrap();
                self.lemma_parse_ok(b);

                let (len, v2) = self.spec_parse(b).unwrap();

                // By definition of spec_parse
                let b_0 = b[0];
                assert(v2 == prepend_byte!(rest.spec_parse(b.drop_first()).unwrap().1, b_0, self.0 - 1));

                // By definition of spec_serialize
                assert(b[0] == get_nth_byte!(v, self.0 - 1));
                assert(b.drop_first() == rest.spec_serialize(v & n_byte_max!(self.0 - 1)).unwrap());
                
                // Expand out everything purely in BV
                // NOTE: this depends on the size of VarUIntResult
                let self_len = self.0;
                assert(
                    0 < self_len <= var_uint_size!() ==>
                    fits_n_bytes!(v, self_len) ==>
                    v == prepend_byte!(
                        v & n_byte_max!(self_len - 1),
                        get_nth_byte!(v, self_len - 1),
                        self_len - 1
                    )
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
                assert(
                    0 < self_len <= var_uint_size!() ==>
                    fits_n_bytes!(rest_parsed, self_len - 1) ==>
                    get_nth_byte!(prepend_byte!(rest_parsed, buf_0, self_len - 1), self_len - 1) == buf_0
                ) by (bit_vector);
            }

            // Then we prove that the rest of buf2 and buf are the same

            // By definition of self.spec_parse(buf)
            assert(v == prepend_byte!(rest_parsed, buf_0, self_len - 1));

            // By some BV reasoning
            assert(rest_parsed == v & n_byte_max!(self_len - 1)) by {
                assert(
                    fits_n_bytes!(rest_parsed, self_len - 1) ==>
                    v == prepend_byte!(rest_parsed, buf_0, self_len - 1) ==>
                    rest_parsed == v & n_byte_max!(self_len - 1)
                ) by (bit_vector);
            }

            // By spec_serialize(rest_parsed) = spec_serialize(v & n_byte_max!(self.0 - 1))
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
                        prepend_byte!(res, byte, len - i),
                        (var_uint_size!() - (i - 1))
                    )

                    // Shows no overflow for the the current iteration
                    &&& n_byte_max!(var_uint_size!() - i) <= var_uint_max_without_first_byte!()
                    &&& prepend_byte!(0, byte, len - i) <= var_uint_max_first_byte!()
                }
            ) by (bit_vector);

            let ghost old_res = res;
            let ghost old_i = i;

            res = prepend_byte!(res, byte, len - i);
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
        let len = self.0;

        // Size overflow or not enough space to store results
        if pos > usize::MAX - var_uint_size!() || data.len() < pos + len {
            return Err(());
        }

        // v is too large (phrased this way to avoid shift underflow)
        if len > 0 && v > n_byte_max!(len) || v != 0 {
            return Err(());
        }

        let ghost original_data = data@;

        let mut i = len;

        assert(v & n_byte_max!(0) == 0) by (bit_vector);
        // assert(data@.subrange(pos + i, pos + len) =~= seq![]);

        while i > 0
            invariant
                0 <= i <= len,
                len <= var_uint_size!(),

                pos <= usize::MAX - var_uint_size!(),
                data.len() >= pos + len,

                data.len() == original_data.len(),

                // At each iteration i, data@.subrange(pos + i, pos + len) is the
                // serialization of the (len - i)-th least significant bytes of v
                data@ =~= seq_splice(
                    original_data,
                    (pos + i) as usize,
                    Self((len - i) as usize).spec_serialize(v & n_byte_max!(len - i)).unwrap(),
                ),
        {
            let byte = get_nth_byte!(v, len - i);
            
            let ghost old_data = data@;
            let ghost old_i = i;

            data.set(pos + i - 1, byte);
            i = i - 1;

            proof {
                // LI:
                // assert(old_data == seq_splice(
                //     original_data,
                //     (pos + old_i) as usize,
                //     Self((len - old_i) as usize).spec_serialize(v & n_byte_max!(len - old_i)).unwrap(),
                // ));

                assert(v & n_byte_max!(len - old_i) <= n_byte_max!(len - old_i)) by (bit_vector);
                assert(v & n_byte_max!(len - i) <= n_byte_max!(len - i)) by (bit_vector);

                Self((len - old_i) as usize).lemma_serialize_ok(v & n_byte_max!(len - old_i));
                Self((len - old_i) as usize).lemma_serialize_ok_len(v & n_byte_max!(len - old_i));
                Self((len - i) as usize).lemma_serialize_ok(v & n_byte_max!(len - i));
                Self((len - i) as usize).lemma_serialize_ok_len(v & n_byte_max!(len - i));

                let old_suffix = Self((len - old_i) as usize).spec_serialize(v & n_byte_max!(len - old_i)).unwrap();
                let suffix = Self((len - i) as usize).spec_serialize(v & n_byte_max!(len - i)).unwrap();

                assert(suffix.drop_first() =~= old_suffix) by {
                    assert(
                        0 <= i < old_i <= len ==>
                        len <= var_uint_size!() ==>
                        (v & n_byte_max!(len - i)) & n_byte_max!(len - old_i) == v & n_byte_max!(len - old_i)
                    ) by (bit_vector);
                }

                assert(byte == suffix[0]) by {
                    assert(
                        0 <= i <= len ==>
                        len <= var_uint_size!() ==>
                        get_nth_byte!(v & n_byte_max!(len - i), len - i - 1)
                            == get_nth_byte!(v, len - (i + 1)) as u8
                    ) by (bit_vector);
                }

                assert(data@[pos + i] == suffix[0]);
            }
        }

        proof {
            self.lemma_serialize_ok(v);
            self.lemma_serialize_ok_len(v);
            assert(v <= n_byte_max!(len) ==> v & n_byte_max!(len) == v) by (bit_vector);
        }
        // assert(data@.subrange(pos as int, pos + len) == self.spec_serialize(v).unwrap());
        // assert(data@ =~= seq_splice(old(data)@, pos, self.spec_serialize(v).unwrap()));

        Ok(len)
    }
}

}
