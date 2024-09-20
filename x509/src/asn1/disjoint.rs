/// Some SpecDisjointFrom and DisjointFrom impls for tagged combinators

use vstd::prelude::*;
use crate::*;

verus! {

/// If T1 and T2 have different tags, then their tagged encodings are disjoint
impl<T1, T2> SpecDisjointFrom<ASN1<T1>> for ASN1<T2> where
    T1: ASN1Tagged + SpecCombinator,
    T2: ASN1Tagged + SpecCombinator,
{
    open spec fn spec_disjoint_from(&self, other: &ASN1<T1>) -> bool {
        self.0.spec_tag() != other.0.spec_tag()
    }

    proof fn spec_parse_disjoint_on(&self, other: &ASN1<T1>, buf: Seq<u8>) {}
}

impl<T1, T2> DisjointFrom<ASN1<T1>> for ASN1<T2> where
    T1: ViewWithASN1Tagged + Combinator,
    <T1 as View>::V: SecureSpecCombinator<SpecResult = <<T1 as Combinator>::Owned as View>::V>,
    <T1 as View>::V: ASN1Tagged,

    T2: ViewWithASN1Tagged + Combinator,
    <T2 as View>::V: SecureSpecCombinator<SpecResult = <<T2 as Combinator>::Owned as View>::V>,
    <T2 as View>::V: ASN1Tagged,
{
    fn disjoint_from(&self, other: &ASN1<T1>) -> bool {
        proof {
            self.0.lemma_view_preserves_tag();
            other.0.lemma_view_preserves_tag();
        }
        !self.0.tag().eq(other.0.tag())
    }
}

/// If T1 and T2 have different tags, then (T1, ...) is disjoint from T2
impl<T1, T2, S> SpecDisjointFrom<(ASN1<T1>, S)> for ASN1<T2> where
    T1: ASN1Tagged + SpecCombinator + SecureSpecCombinator,
    T2: ASN1Tagged + SpecCombinator,
    S: SpecCombinator,
{
    open spec fn spec_disjoint_from(&self, other: &(ASN1<T1>, S)) -> bool {
        self.0.spec_tag() != other.0.0.spec_tag()
    }

    proof fn spec_parse_disjoint_on(&self, other: &(ASN1<T1>, S), buf: Seq<u8>) {}
}

impl<T1, T2, S> DisjointFrom<(ASN1<T1>, S)> for ASN1<T2> where
    T1: ViewWithASN1Tagged + Combinator,
    <T1 as View>::V: SecureSpecCombinator<SpecResult = <<T1 as Combinator>::Owned as View>::V>,
    <T1 as View>::V: ASN1Tagged,

    T2: ViewWithASN1Tagged + Combinator,
    <T2 as View>::V: SecureSpecCombinator<SpecResult = <<T2 as Combinator>::Owned as View>::V>,
    <T2 as View>::V: ASN1Tagged,

    S: Combinator,
    S::V: SecureSpecCombinator<SpecResult = <<S as Combinator>::Owned as View>::V>,
{
    fn disjoint_from(&self, other: &(ASN1<T1>, S)) -> bool {
        proof {
            self.0.lemma_view_preserves_tag();
            other.0.0.lemma_view_preserves_tag();
        }
        !self.0.tag().eq(other.0.tag())
    }
}

// NOTE: We can't do impl<T1, T2, S> SpecDisjointFrom<ASN1<T2>> for (ASN1<T1>, S) since
// both SpecDisjointFrom and tuple type is not defined in this crate
// For this purpose, use Pair instead of the native tuple type

/// Same as above, but uses a custom
impl<T1, T2, S> SpecDisjointFrom<Pair<ASN1<T1>, S>> for ASN1<T2> where
    T1: ASN1Tagged + SecureSpecCombinator,
    T2: ASN1Tagged + SecureSpecCombinator,
    S: SecureSpecCombinator,
{
    open spec fn spec_disjoint_from(&self, other: &Pair<ASN1<T1>, S>) -> bool {
        self.0.spec_tag() != other.0.0.spec_tag()
    }

    proof fn spec_parse_disjoint_on(&self, other: &Pair<ASN1<T1>, S>, buf: Seq<u8>) {}
}

impl<T1, T2, S> DisjointFrom<Pair<ASN1<T1>, S>> for ASN1<T2> where
    T1: ViewWithASN1Tagged + Combinator,
    <T1 as View>::V: SecureSpecCombinator<SpecResult = <<T1 as Combinator>::Owned as View>::V>,
    <T1 as View>::V: ASN1Tagged,

    T2: ViewWithASN1Tagged + Combinator,
    <T2 as View>::V: SecureSpecCombinator<SpecResult = <<T2 as Combinator>::Owned as View>::V>,
    <T2 as View>::V: ASN1Tagged,

    S: Combinator,
    S::V: SecureSpecCombinator<SpecResult = <<S as Combinator>::Owned as View>::V>,
{
    fn disjoint_from(&self, other: &Pair<ASN1<T1>, S>) -> bool {
        proof {
            self.0.lemma_view_preserves_tag();
            other.0.0.lemma_view_preserves_tag();
        }
        !self.0.tag().eq(other.0.tag())
    }
}

/// The other direction of the above
impl<T1, T2, S> SpecDisjointFrom<ASN1<T2>> for Pair<ASN1<T1>, S> where
    T1: ASN1Tagged + SecureSpecCombinator,
    T2: ASN1Tagged + SecureSpecCombinator,
    S: SecureSpecCombinator,
{
    open spec fn spec_disjoint_from(&self, other: &ASN1<T2>) -> bool {
        other.0.spec_tag() != self.0.0.spec_tag()
    }

    proof fn spec_parse_disjoint_on(&self, other: &ASN1<T2>, buf: Seq<u8>) {}
}

impl<T1, T2, S> DisjointFrom<ASN1<T2>> for Pair<ASN1<T1>, S> where
    T1: ViewWithASN1Tagged + Combinator,
    <T1 as View>::V: SecureSpecCombinator<SpecResult = <<T1 as Combinator>::Owned as View>::V>,
    <T1 as View>::V: ASN1Tagged,

    T2: ViewWithASN1Tagged + Combinator,
    <T2 as View>::V: SecureSpecCombinator<SpecResult = <<T2 as Combinator>::Owned as View>::V>,
    <T2 as View>::V: ASN1Tagged,

    S: Combinator,
    S::V: SecureSpecCombinator<SpecResult = <<S as Combinator>::Owned as View>::V>,
{
    fn disjoint_from(&self, other: &ASN1<T2>) -> bool {
        proof {
            other.0.lemma_view_preserves_tag();
            self.0.0.lemma_view_preserves_tag();
        }
        !other.0.tag().eq(self.0.tag())
    }
}

/// If T2 and T3 are both disjoint from T1, then
/// something like Optional<T1, Optional<T2, T3>> is doable
impl<T1, T2, T3> SpecDisjointFrom<T1> for Optional<T2, T3> where
    T1: SecureSpecCombinator,
    T2: SecureSpecCombinator,
    T3: SecureSpecCombinator,
    T2: SpecDisjointFrom<T1>,
    T3: SpecDisjointFrom<T1>,
    T3: SpecDisjointFrom<T2>,
{
    open spec fn spec_disjoint_from(&self, other: &T1) -> bool {
        self.0.spec_disjoint_from(other) &&
        self.1.spec_disjoint_from(other)
    }

    proof fn spec_parse_disjoint_on(&self, other: &T1, buf: Seq<u8>) {
        self.0.spec_parse_disjoint_on(other, buf);
        self.1.spec_parse_disjoint_on(other, buf);
    }
}

impl<T1, T2, T3> DisjointFrom<T1> for Optional<T2, T3> where
    T1: Combinator,
    T1::V: SecureSpecCombinator<SpecResult = <<T1 as Combinator>::Owned as View>::V>,

    T2: Combinator,
    T2::V: SecureSpecCombinator<SpecResult = <<T2 as Combinator>::Owned as View>::V>,

    T3: Combinator,
    T3::V: SecureSpecCombinator<SpecResult = <<T3 as Combinator>::Owned as View>::V>,

    T2::V: SpecDisjointFrom<T1::V>,
    T3::V: SpecDisjointFrom<T1::V>,
    T3::V: SpecDisjointFrom<T2::V>,

    T2: DisjointFrom<T1>,
    T3: DisjointFrom<T1>,
    T3: DisjointFrom<T2>,
{
    fn disjoint_from(&self, other: &T1) -> bool {
        self.0.disjoint_from(other) &&
        self.1.disjoint_from(other)
    }
}

impl<T> SpecDisjointFrom<ASN1<T>> for End where
    T: ASN1Tagged + SpecCombinator,
{
    open spec fn spec_disjoint_from(&self, other: &ASN1<T>) -> bool { true }
    proof fn spec_parse_disjoint_on(&self, other: &ASN1<T>, buf: Seq<u8>) {}
}

impl<T> DisjointFrom<ASN1<T>> for End where
    T: ViewWithASN1Tagged + Combinator,
    <T as View>::V: SecureSpecCombinator<SpecResult = <<T as Combinator>::Owned as View>::V>,
    <T as View>::V: ASN1Tagged,
{
    fn disjoint_from(&self, other: &ASN1<T>) -> bool { true }
}

}
