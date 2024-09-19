use vstd::prelude::*;
use crate::utils::*;

use super::clone::*;
use super::vest::*;

verus! {

/// Essentially doing OrdChoice((C1, C2), C2),
/// but the result is mapped through
///   Left((A, B)) <-> (Some(A), B)
///   Right(B) <-> (None, B)
pub struct Optional<C1, C2>(pub C1, pub C2);

pub struct OptionalValue<T1, T2>(pub Option<T1>, pub T2);

impl<C1: Combinator, C2: Combinator> Optional<C1, C2> where
    C1::V: SecureSpecCombinator<SpecResult = <C1::Owned as View>::V>,
    C2::V: SecureSpecCombinator<SpecResult = <C2::Owned as View>::V> + SpecDisjointFrom<C1::V>,
{
    pub fn new(c1: C1, c2: C2) -> Self {
        Optional(c1, c2)
    }
}

impl<C1: View, C2: View> View for Optional<C1, C2> {
    type V = Optional<C1::V, C2::V>;

    open spec fn view(&self) -> Self::V {
        Optional(self.0@, self.1@)
    }
}

impl<T1: View, T2: View> View for OptionalValue<T1, T2> {
    type V = (Option<T1::V>, T2::V);

    open spec fn view(&self) -> Self::V {
        (match self.0 {
            Some(v) => Some(v@),
            None => None,
        }, self.1@)
    }
}

// impl<C1: PolyfillCloneCombinator, C2: PolyfillCloneCombinator> PolyfillCloneCombinator for Optional<C1, C2> where
//     <C1 as View>::V: SecureSpecCombinator<SpecResult = <C1::Owned as View>::V>,
//     <C2 as View>::V: SecureSpecCombinator<SpecResult = <C2::Owned as View>::V>,
// {
//     fn clone(&self) -> Self {
//         Optional(self.0.clone(), self.1.clone())
//     }
// }

// impl<C1, C2> SpecDisjointFrom<(C1, C2)> for C2 where
//     C1: SpecCombinator,
//     C2: SpecCombinator + SpecDisjointFrom<C1>,
// {
//     spec fn spec_disjoint_from(&self, other: &(C1, C2)) -> bool {
//         self.spec_disjoint_from(&other.1)
//     }

//     proof fn spec_parse_disjoint_on(&self, other: &(C1, C2), buf: Seq<u8>) {
//         assume(false);
//     }
// }

impl<C1, C2> SpecCombinator for Optional<C1, C2> where
    C1: SecureSpecCombinator,
    C2: SecureSpecCombinator + SpecDisjointFrom<C1>,
{
    type SpecResult = (Option<C1::SpecResult>, C2::SpecResult);

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()>
    {
        match new_spec_optional_inner(self.0, self.1).spec_parse(s) {
            Ok((n, Either::Left((v1, v2)))) => Ok((n, (Some(v1), v2))),
            Ok((n, Either::Right((v, _)))) => Ok((n, (None, v))),
            Err(()) => Err(()),
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        new_spec_optional_inner(self.0, self.1).spec_parse_wf(s);
    }

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()>
    {
        match v {
            (Some(v1), v2) => new_spec_optional_inner(self.0, self.1).spec_serialize(Either::Left((v1, v2))),
            (None, v2) => new_spec_optional_inner(self.0, self.1).spec_serialize(Either::Right((v2, seq![]))),
        }
    }
}

impl<C1, C2> SecureSpecCombinator for Optional<C1, C2> where
    C1: SecureSpecCombinator,
    C2: SecureSpecCombinator + SpecDisjointFrom<C1>
{
    open spec fn spec_is_prefix_secure() -> bool {
        C1::spec_is_prefix_secure() && C2::spec_is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        let mapped = match v {
            (Some(v1), v2) => Either::Left((v1, v2)),
            (None, v2) => Either::Right((v2, seq![])),
        };

        new_spec_optional_inner(self.0, self.1).theorem_serialize_parse_roundtrip(mapped);
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        new_spec_optional_inner(self.0, self.1).theorem_parse_serialize_roundtrip(buf);
        assert(self.spec_parse(buf) matches Ok((n, v)) ==> self.spec_serialize(v).unwrap() == buf.subrange(0, n as int));
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        if C2::spec_is_prefix_secure() {
            new_spec_optional_inner(self.0, self.1).lemma_prefix_secure(s1, s2);
        }
    }
}

// <<C1 as vstd::string::View>::V as vest::properties::SpecCombinator>::SpecResult == <<C1 as vest::properties::Combinator>::Owned as vstd::string::View>::V

impl<C1, C2> Combinator for Optional<C1, C2> where
    C1: Combinator,
    C2: Combinator + DisjointFrom<C1>,

    C1::V: SecureSpecCombinator<SpecResult = <C1::Owned as View>::V>,
    C2::V: SecureSpecCombinator<SpecResult = <C2::Owned as View>::V> + SpecDisjointFrom<C1::V>,

    // for <'a> &'a C1: Combinator,
    // for <'a> &'a C2: Combinator,
    // for <'a> &'a C2: DisjointFrom<&'a C1>,
{
    type Result<'a> = OptionalValue<C1::Result<'a>, C2::Result<'a>>;
    type Owned = OptionalValue<C1::Owned, C2::Owned>;

    open spec fn spec_length(&self) -> Option<usize> {
        None
    }

    fn length(&self) -> Option<usize> {
        None
    }

    fn exec_is_prefix_secure() -> bool {
        C1::exec_is_prefix_secure() && C2::exec_is_prefix_secure()
    }

    open spec fn parse_requires(&self) -> bool {
        &&& self.0.parse_requires()
        &&& self.1.parse_requires()
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ()>) {
        match OrdChoice((&self.0, &self.1), (&self.1, BytesN::<0>)).parse(s)? {
            (n, Either::Left((v1, v2))) => Ok((n, OptionalValue(Some(v1), v2))),
            (n, Either::Right((v, _))) => Ok((n, OptionalValue(None, v))),
        }
    }

    open spec fn serialize_requires(&self) -> bool {
        &&& self.0.serialize_requires()
        &&& self.1.serialize_requires()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, ()>) {
        let c = OrdChoice((&self.0, &self.1), (&self.1, BytesN::<0>));
        let len = match v {
            OptionalValue(Some(v1), v2) => c.serialize(Either::Left((v1, v2)), data, pos),
            OptionalValue(None, v2) => c.serialize(Either::Right((v2, &[])), data, pos),
        }?;

        assert(data@ =~= seq_splice(old(data)@, pos, self@.spec_serialize(v@).unwrap()));

        Ok(len)
    }
}

type OptionalInner<C1, C2> = OrdChoice<(C1, C2), (C2, BytesN<0>)>;

pub open spec fn new_spec_optional_inner<C1, C2>(c1: C1, c2: C2) -> OptionalInner<C1, C2> {
    OrdChoice((c1, c2), (c2, BytesN::<0>))
}

// fn new_optional_inner<C1, C2: PolyfillCloneCombinator>(c1: C1, c2: C2) -> OptionalInner<C1, C2>
//     where
//         <C2 as View>::V: SecureSpecCombinator<SpecResult = <C2::Owned as View>::V>,
// {
//     OrdChoice::new((c1, c2.clone()), (c2, BytesN::<0>))
// }

}
