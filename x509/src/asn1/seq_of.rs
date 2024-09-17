use vstd::prelude::*;

use super::clone::*;
use super::vest::*;
use super::octet_string::*;
use super::tag::*;
use super::repeat::*;
use super::depend::*;
use super::len::*;
use super::explicit::*;

verus! {

/// SEQUENCE OF in ASN.1
#[derive(Debug)]
pub struct SequenceOf<C>(pub C);

pub type SequenceOfValue<'a, C> = RepeatResult<'a, C>;
pub type SequenceOfValueOwned<C> = RepeatResultOwned<C>;

impl<C: View> View for SequenceOf<C>
{
    type V = SequenceOf<<C as View>::V>;

    open spec fn view(&self) -> Self::V {
        SequenceOf(self.0@)
    }
}

impl<C> ASN1Tagged for SequenceOf<C> {
    open spec fn spec_tag(&self) -> TagValue {
        TagValue {
            class: TagClass::Universal,
            form: TagForm::Constructed,
            num: 0x10,
        }
    }

    fn tag(&self) -> TagValue {
        TagValue {
            class: TagClass::Universal,
            form: TagForm::Constructed,
            num: 0x10,
        }
    }
}

impl<C: View> ViewWithASN1Tagged for SequenceOf<C> {
    proof fn lemma_view_preserves_tag(&self) {}
}

/// TODO: putting it here to avoid a Verus issue
impl<T: PolyfillCloneCombinator> PolyfillCloneCombinator for SequenceOf<T> where
    <T as View>::V: SecureSpecCombinator<SpecResult = <T::Owned as View>::V>,
    for<'a> <T as Combinator>::Result<'a>: PolyfillClone,
{
    fn clone(&self) -> Self {
        SequenceOf(self.0.clone())
    }
}

impl<C: SecureSpecCombinator + SpecCombinator> SpecCombinator for SequenceOf<C> {
    type SpecResult = Seq<C::SpecResult>;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        ExplicitTag(self.spec_tag(), Repeat(self.0)).spec_parse(s)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {}

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        ExplicitTag(self.spec_tag(), Repeat(self.0)).spec_serialize(v)
    }
}

impl<C: SecureSpecCombinator + SpecCombinator> SecureSpecCombinator for SequenceOf<C> {
    open spec fn spec_is_prefix_secure() -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        ExplicitTag(self.spec_tag(), Repeat(self.0)).theorem_serialize_parse_roundtrip(v);
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        ExplicitTag(self.spec_tag(), Repeat(self.0)).theorem_parse_serialize_roundtrip(buf);
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        ExplicitTag(self.spec_tag(), Repeat(self.0)).lemma_prefix_secure(s1, s2);
    }
}

impl<C: PolyfillCloneCombinator + Combinator> Combinator for SequenceOf<C> where
    <C as View>::V: SecureSpecCombinator<SpecResult = <C::Owned as View>::V>,
    for<'a> C::Result<'a>: PolyfillClone,
{
    type Result<'a> = SequenceOfValue<'a, C>;
    type Owned = SequenceOfValueOwned<C>;

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
        &&& <C as View>::V::spec_is_prefix_secure()
        &&& self.0.parse_requires()
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ()>) {
        let c = ExplicitTag(self.tag(), Repeat(self.0.clone()));
        // reveal(ExplicitTag::spec_length);
        // assert(c.1.parse_requires());
        // assert(c.parse_requires() ==> ttttest());
        assert(c.spec_length().is_none());
        // assert(c.parse_requires() ==> c.1.parse_requires());
        assume(false);
        c.parse(s)
    }

    open spec fn serialize_requires(&self) -> bool {
        &&& <C as View>::V::spec_is_prefix_secure()
        &&& self.0.serialize_requires()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, ()>) {
        assume(false);
        ExplicitTag(self.tag(), Repeat(self.0.clone())).serialize(v, data, pos)
    }
}

}
