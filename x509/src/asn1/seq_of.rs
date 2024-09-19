use vstd::prelude::*;

use crate::common::*;

use super::octet_string::*;
use super::tag::*;
use super::len::*;
use super::explicit::*;

verus! {

/// SEQUENCE OF in ASN.1
#[derive(Debug)]
pub struct SequenceOf<C>(pub C);

pub type SequenceOfValue<T> = RepeatResult<T>;
pub type SequenceOfValueOwned<T> = RepeatResultOwned<T>;

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

impl<C: Combinator> Combinator for SequenceOf<C> where
    <C as View>::V: SecureSpecCombinator<SpecResult = <C::Owned as View>::V>,
    for<'a> C::Result<'a>: PolyfillClone,
{
    type Result<'a> = SequenceOfValue<C::Result<'a>>;
    type Owned = SequenceOfValueOwned<C::Owned>;

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
        ExplicitTag(self.tag(), Repeat(&self.0)).parse(s)
    }

    open spec fn serialize_requires(&self) -> bool {
        &&& <C as View>::V::spec_is_prefix_secure()
        &&& self.0.serialize_requires()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, ()>) {
        ExplicitTag(self.tag(), Repeat(&self.0)).serialize(v, data, pos)
    }
}

}
