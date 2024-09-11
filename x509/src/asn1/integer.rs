use vstd::prelude::*;

use crate::polyfill::*;
use crate::vest::*;
use crate::asn1::*;

verus! {

pub type IntegerSize = VarUIntResult;
pub type IntegerValue = VarIntResult;

#[allow(unused_macros)]
macro_rules! fits_n_bytes_signed {
    ($v:expr, $n:expr) => {
        n_byte_min_signed!($n) <= $v && $v <= n_byte_max_signed!($n)
    };
}

/// Defines n being the minimum number of bytes required to represent v (as a signed integer)
/// This enforces some integer encoding rules in DER:
/// 1. At least 1 byte is required (even if v == 0)
/// 2. v as a signed integer can fit into n bytes
/// 3. v as a signed integer cannot fit into (n - 1) bytes
/// 
/// NOTE: signed version of is_min_num_bytes_unsigned
pub open spec fn is_min_num_bytes_signed(v: IntegerValue, n: IntegerSize) -> bool {
    &&& n > 0
    &&& n <= var_uint_size!()
    &&& if v == 0 {
        n == 1
    } else {
        &&& fits_n_bytes_signed!(v, n)
        &&& !fits_n_bytes_signed!(v, n - 1)
    }
}

/// Exec version of is_min_num_bytes_signed
pub fn is_min_num_bytes_signed_exec(v: IntegerValue, n: IntegerSize) -> (res: bool)
    ensures res == is_min_num_bytes_signed(v, n)
{
    n > 0 &&
    n <= var_uint_size!() &&
    if v == 0 {
        n == 1
    } else {
        fits_n_bytes_signed!(v, n) &&
        !fits_n_bytes_signed!(v, n - 1)
    }
}

pub open spec fn min_num_bytes_signed(v: IntegerValue) -> IntegerSize
{
    choose |n| is_min_num_bytes_signed(v, n)
}

/// A helper induction lemma
proof fn lemma_well_ordering(p: spec_fn(IntegerSize) -> bool, n: IntegerSize)
    requires p(n) && !p(0)
    ensures exists |i: IntegerSize| 0 < i <= n && (#[trigger] p(i)) && !p((i - 1) as IntegerSize)
    decreases n
{
    if n > 1 && p((n - 1) as IntegerSize) {
        lemma_well_ordering(p, (n - 1) as IntegerSize);
    }
}

/// min_num_bytes_signed exists
/// TODO: Exactly the same proof as min_num_bytes_unsigned; refactor?
pub proof fn lemma_min_num_bytes_signed_exists(v: IntegerValue)
    ensures exists |n| is_min_num_bytes_signed(v, n)
{
    if v == 0 {
        assert(is_min_num_bytes_signed(v, 1));
    } else {
        assert(v != 0 ==> !fits_n_bytes_signed!(v, 0)) by (bit_vector);
        assert(fits_n_bytes_signed!(v, var_uint_size!())) by (bit_vector);

        let fits_n = |n: IntegerSize| fits_n_bytes_signed!(v, n);
        let bytes = choose |i: IntegerSize| 0 < i <= var_uint_size!() && #[trigger] fits_n(i) && !fits_n((i - 1) as IntegerSize);

        lemma_well_ordering(fits_n, var_uint_size!());
        assert(is_min_num_bytes_signed(v, bytes));
    }
}

/// min_num_bytes_signed is unique
pub proof fn lemma_min_num_bytes_signed_unique(v: IntegerValue)
    ensures forall |n1, n2|
        is_min_num_bytes_signed(v, n1) &&
        is_min_num_bytes_signed(v, n2) ==> n1 == n2
{
    assert forall |n1, n2|
        is_min_num_bytes_signed(v, n1) &&
        is_min_num_bytes_signed(v, n2)
    implies n1 == n2 by {
        // By contradiction: if n2 < n1 or n1 < n2, then we can derive false by BV reasoning
        assert(n2 < n1 <= var_uint_size!() ==> !(fits_n_bytes_signed!(v, n2) && !fits_n_bytes_signed!(v, n1 - 1))) by (bit_vector);
        assert(n1 < n2 <= var_uint_size!() ==> !(fits_n_bytes_signed!(v, n1) && !fits_n_bytes_signed!(v, n2 - 1))) by (bit_vector);
    };
}

/// Exec version of min_num_bytes_signed
pub fn min_num_bytes_signed_exec(v: IntegerValue) -> (res: IntegerSize)
    ensures is_min_num_bytes_signed(v, res)
{
    let mut n = var_uint_size!();

    assert(n == var_uint_size!() ==> fits_n_bytes_signed!(v, n)) by (bit_vector);

    while n > 0
        invariant
            0 <= n <= var_uint_size!(),
            fits_n_bytes_signed!(v, n),
    {
        if !fits_n_bytes_signed!(v, n - 1) {
            assert(v == 0 && !fits_n_bytes_signed!(v, n - 1) ==> n == 1) by (bit_vector);
            return n;
        }
        n = n - 1;
    }

    assert(fits_n_bytes_signed!(v, 0) ==> v == 0) by (bit_vector);
    
    return 1;
}

/// Combinator for ASN.1 integers (without the preceding tag)
/// This combinator uses IntegerInner with the additional constraint
/// of is_min_num_bytes_signed
pub struct Integer;

impl View for Integer {
    type V = Integer;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecCombinator for Integer {
    type SpecResult = IntegerValue;

    /// Same as new_spec_integer_inner(), but filters out tuples (n, v)
    /// where v is *not* the minimum number of bytes required to represent v
    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        match new_spec_integer_inner().spec_parse(s) {
            Ok((len, (n, v))) => {
                if is_min_num_bytes_signed(v, n) {
                    Ok((len, v))
                } else {
                    Err(())
                }
            }
            Err(..) => Err(()),
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {}

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        new_spec_integer_inner().spec_serialize((min_num_bytes_signed(v), v))
    }
}

impl SecureSpecCombinator for Integer {
    open spec fn spec_is_prefix_secure() -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        new_spec_integer_inner().theorem_serialize_parse_roundtrip((min_num_bytes_signed(v), v));
        lemma_min_num_bytes_signed_exists(v);
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        new_spec_integer_inner().theorem_parse_serialize_roundtrip(buf);

        if let Ok((_, (n, v))) = new_spec_integer_inner().spec_parse(buf) {
            lemma_min_num_bytes_signed_unique(v);
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        new_spec_integer_inner().lemma_prefix_secure(s1, s2);
    }
}

impl Combinator for Integer {
    type Result<'a> = IntegerValue;
    type Owned = IntegerValue;

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
        let (len, (n, v)) = new_integer_inner().parse(s)?;

        if is_min_num_bytes_signed_exec(v, n) {
            Ok((len, v))
        } else {
            Err(())
        }
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, ()>) {
        proof {
            lemma_min_num_bytes_signed_unique(v);
        }
        new_integer_inner().serialize((min_num_bytes_signed_exec(v), v), data, pos)
    }
}

/// This is a function that takes in a VarUIntResult (`l`)
/// and returns a VarInt combinator that reads `l` bytes
pub struct IntegerCont;

impl Continuation for IntegerCont {
    type Input<'a> = VarUIntResult;
    type Output = VarInt;

    fn apply<'a>(&self, i: Self::Input<'a>) -> (o: Self::Output) {
        VarInt(i as usize)
    }

    open spec fn requires<'a>(&self, i: Self::Input<'a>) -> bool {
        true
    }

    open spec fn ensures<'a>(&self, i: Self::Input<'a>, o: Self::Output) -> bool {
        o == VarInt(i as usize)
    }
}

/// A combinator that parses (n, v) where v is a VarInt parsed from n bytes
/// This does not check if n is the minimum number of bytes required to represent v
type SpecIntegerInner = SpecDepend<Preceded<Tag<U8, u8>, Length>, VarInt>;
type IntegerInner = Depend<Preceded<Tag<U8, u8>, Length>, VarInt, IntegerCont>;

pub open spec fn new_spec_integer_inner() -> SpecIntegerInner {
    let ghost spec_snd = |l| {
        VarInt(l as usize)
    };

    SpecDepend {
        fst: Preceded(Tag::spec_new(U8, 0x02), Length),
        snd: spec_snd,
    }
}

fn new_integer_inner() -> (res: IntegerInner)
    ensures res.view() == new_spec_integer_inner()
{
    let ghost spec_snd = |l| {
        VarInt(l as usize)
    };

    Depend {
        fst: Preceded(Tag::new(U8, 0x02), Length),
        snd: IntegerCont,
        spec_snd: Ghost(spec_snd),
    }
}

}
