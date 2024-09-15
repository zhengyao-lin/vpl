use vstd::prelude::*;

use super::vest::*;
use super::tag::*;
use super::depend::*;
use super::len::*;
use super::clone::*;

verus! {

/// Explicit tagging wrapps the inner combinator in a new TLV tuple
/// TODO: the spec of this combinator is hard to read
pub struct ExplicitTag<T>(pub TagValue, pub T);

impl<T: ASN1Tagged> ASN1Tagged for ExplicitTag<T> {
    open spec fn spec_tag(&self) -> TagValue {
        self.0
    }

    fn tag(&self) -> TagValue {
        self.0.clone()
    }
}

impl<T: View> View for ExplicitTag<T> {
    type V = ExplicitTag<T::V>;

    open spec fn view(&self) -> Self::V {
        ExplicitTag(self.0, self.1@)
    }
}

impl<T: SpecCombinator> SpecCombinator for ExplicitTag<T> {
    type SpecResult = T::SpecResult;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        match new_spec_explicit_tag_inner(self.1).spec_parse(s) {
            Ok((len, (_, v))) => Ok((len, v)),
            Err(..) => Err(()),
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        new_spec_explicit_tag_inner(self.1).spec_parse_wf(s)
    }

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        match self.1.spec_serialize(v) {
            // Need to compute the inner serialized length first
            Ok(buf) => new_spec_explicit_tag_inner(self.1).spec_serialize((buf.len() as LengthValue, v)),
            Err(..) => Err(()),
        }
    }
}

impl<T: SecureSpecCombinator> SecureSpecCombinator for ExplicitTag<T> {
    open spec fn spec_is_prefix_secure() -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        if let Ok(buf) = self.1.spec_serialize(v) {
            new_spec_explicit_tag_inner(self.1).theorem_serialize_parse_roundtrip((buf.len() as LengthValue, v))
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        new_spec_explicit_tag_inner(self.1).theorem_parse_serialize_roundtrip(buf)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        new_spec_explicit_tag_inner(self.1).lemma_prefix_secure(s1, s2)
    }
}

impl<T: PolyfillClone + ASN1Tagged + Combinator> Combinator for ExplicitTag<T> where
    T: SecureSpecCombinator<SpecResult = <<T as Combinator>::Owned as View>::V>,
    <T as View>::V: SecureSpecCombinator<SpecResult = <<T as Combinator>::Owned as View>::V>,
    <T as View>::V: ASN1Tagged,
    for<'a> T::Result<'a>: PolyfillClone,
{
    type Result<'a> = T::Result<'a>;
    type Owned = T::Owned;

    open spec fn spec_length(&self) -> Option<usize> {
        None
    }

    fn length(&self) -> Option<usize> {
        None
    }

    fn exec_is_prefix_secure() -> bool {
        true
    }

    open spec fn parse_requires(&self) -> bool {
        // Extra clone coming from the exec parse() function
        self.1.spec_clone().spec_clone().parse_requires()
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ()>) {
        proof {
            lemma_new_explicit_tag_inner_parse_requires(self.1.spec_clone());
        }
        let (len, (_, v)) = new_explicit_tag_inner(self.1.clone()).parse(s)?;
        Ok((len, v))
    }

    open spec fn serialize_requires(&self) -> bool {
        self.1.serialize_requires() &&
        self.1.spec_clone().spec_clone().serialize_requires()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, ()>) {
        proof {
            lemma_new_explicit_tag_inner_serialize_requires(self.1.spec_clone());
        }

        // TODO: can we avoid serializing twice?
        let v_cloned = v.clone();
        let len = self.1.serialize(v_cloned, data, pos)?;
        let final_len = new_explicit_tag_inner(self.1.clone()).serialize((len as LengthValue, v), data, pos)?;

        if pos < data.len() && final_len < data.len() - pos {
            assert(data@ =~= seq_splice(old(data)@, pos, self@.spec_serialize(v@).unwrap()));
            return Ok(final_len);
        }

        Err(())
    }
}

/// The function |i| AndThen<Bytes, T>
pub struct ExplicitTagCont<T>(pub T);

impl<T: PolyfillClone> Continuation for ExplicitTagCont<T> {
    type Input<'a> = LengthValue;
    type Output = AndThen<Bytes, T>;

    fn apply<'a>(&self, i: Self::Input<'a>) -> (o: Self::Output) {
        let res = AndThen(Bytes(i as usize), self.0.clone());
        // TODO: requiring this seems to be a Verus bug
        assert(self.ensures(i, res));
        res
    }

    open spec fn requires<'a>(&self, i: Self::Input<'a>) -> bool {
        true
    }

    open spec fn ensures<'a>(&self, i: Self::Input<'a>, o: Self::Output) -> bool {
        // TODO: here we are cheating a bit: maybe we should use two output types (T and <T as View>::V) instead
        o == AndThen(Bytes(i as usize), self.0.spec_clone())
    }
}

type SpecExplicitTagInner<T> = SpecDepend<Length, AndThen<Bytes, T>>;
type ExplicitTagInner<T> = Depend<Length, AndThen<Bytes, T>, ExplicitTagCont<T>>;

/// SpecDepend version of new_explicit_tag_inner
pub open spec fn new_spec_explicit_tag_inner<T: SpecCombinator>(inner: T) -> SpecExplicitTagInner<T> {
    SpecDepend {
        fst: Length,
        snd: |l| {
            AndThen(Bytes(l as usize), inner)
        },
    }
}

/// Spec version of new_explicit_tag_inner
pub open spec fn new_explicit_tag_inner_spec<T: PolyfillClone + Combinator>(inner: T) -> ExplicitTagInner<T> where
    T: SecureSpecCombinator<SpecResult = <<T as Combinator>::Owned as View>::V>,
    <T as View>::V: SecureSpecCombinator<SpecResult = <<T as Combinator>::Owned as View>::V>,
    <T as View>::V: ASN1Tagged,
{
    Depend {
        fst: Length,
        snd: ExplicitTagCont(inner),
        spec_snd: Ghost(|l| {
            AndThen(Bytes(l as usize), inner@)
        }),
    }
}

/// Reduce parse_requires() of ExplicitTagInner to
/// the parse_requires() of the inner combinator
proof fn lemma_new_explicit_tag_inner_parse_requires<T: PolyfillClone + Combinator>(inner: T) where
    T: SecureSpecCombinator<SpecResult = <<T as Combinator>::Owned as View>::V>,
    <T as View>::V: SecureSpecCombinator<SpecResult = <<T as Combinator>::Owned as View>::V>,
    <T as View>::V: ASN1Tagged,

    requires inner.spec_clone().parse_requires(),
    ensures new_explicit_tag_inner_spec(inner).parse_requires(),
{
    inner.lemma_spec_clone();
}

/// Similar to above, but for serialize_requires()
proof fn lemma_new_explicit_tag_inner_serialize_requires<T: PolyfillClone + Combinator>(inner: T) where
    T: SecureSpecCombinator<SpecResult = <<T as Combinator>::Owned as View>::V>,
    <T as View>::V: SecureSpecCombinator<SpecResult = <<T as Combinator>::Owned as View>::V>,
    <T as View>::V: ASN1Tagged,

    requires inner.spec_clone().serialize_requires(),
    ensures new_explicit_tag_inner_spec(inner).serialize_requires(),
{
    inner.lemma_spec_clone();
}

fn new_explicit_tag_inner<T: PolyfillClone + Combinator>(inner: T) -> (res: ExplicitTagInner<T>) where
    T: SecureSpecCombinator<SpecResult = <<T as Combinator>::Owned as View>::V>,
    <T as View>::V: SecureSpecCombinator<SpecResult = <<T as Combinator>::Owned as View>::V>,
    <T as View>::V: ASN1Tagged,
    
    ensures
        res == new_explicit_tag_inner_spec(inner),
        res@ == new_spec_explicit_tag_inner(inner@),
{
    Depend {
        fst: Length,
        snd: ExplicitTagCont(inner),
        spec_snd: Ghost(|l| {
            AndThen(Bytes(l as usize), inner@)
        }),
    }
}

}
