use vstd::prelude::*;

use polyfill::*;

use super::vest::*;
use super::var_int::*;
use super::len::*;
use super::bounds::*;
use super::depend::*;

verus! {

pub type IntegerValue = VarIntResult;

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
        lemma_min_num_bytes_signed(v);
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        new_spec_integer_inner().theorem_parse_serialize_roundtrip(buf);

        if let Ok((_, (n, v))) = new_spec_integer_inner().spec_parse(buf) {
            lemma_min_num_bytes_signed(v);
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
            lemma_min_num_bytes_signed(v);
        }
        new_integer_inner().serialize((min_num_bytes_signed_exec(v), v), data, pos)
    }
}

/// This is a function that takes in a VarUIntResult (`l`)
/// and returns a VarInt combinator that reads `l` bytes
struct IntegerCont;

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
type SpecIntegerInner = SpecDepend<Length, VarInt>;
type IntegerInner = Depend<Length, VarInt, IntegerCont>;

pub open spec fn new_spec_integer_inner() -> SpecIntegerInner {
    let ghost spec_snd = |l| {
        VarInt(l as usize)
    };

    SpecDepend {
        fst: Length,
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
        fst: Length,
        snd: IntegerCont,
        spec_snd: Ghost(spec_snd),
    }
}

}
