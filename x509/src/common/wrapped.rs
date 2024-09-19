use std::marker::PhantomData;

use vstd::prelude::*;

use super::*;

verus! {

/// Sometimes it is useful to wrap an existing combinator
/// within a Mapped combinator so that the SpecFrom trait
/// works better
pub type Wrapped<C> = Mapped<C, IdentityMapper<C>>;

pub fn new_wrapped<C: Combinator>(c: C) -> Wrapped<C> where
    C::V: SecureSpecCombinator<SpecResult = <C::Owned as View>::V>,
{
    Mapped {
        inner: c,
        mapper: IdentityMapper::new(),
    }
}

/// An identity mapper that does not change the parsed object
/// Used in situations when we need prove U: DisjointFrom<Mapped<...>>
/// in which case we can wrap U in Mapped and use existing impls
#[derive(Debug)]
pub struct IdentityMapper<C>(pub PhantomData<C>);

impl<C: View> View for IdentityMapper<C> {
    type V = IdentityMapper<C::V>;

    open spec fn view(&self) -> Self::V {
        IdentityMapper(PhantomData)
    }
}

impl<C> IdentityMapper<C> {
    pub fn new() -> Self {
        IdentityMapper(PhantomData)
    }
}

impl<C: SpecCombinator> SpecIso for IdentityMapper<C> {
    type Src = C::SpecResult;
    type Dst = C::SpecResult;

    proof fn spec_iso(s: Self::Src) {}
    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl<C: Combinator> Iso for IdentityMapper<C> where
    C::V: SecureSpecCombinator<SpecResult = <C::Owned as View>::V>,
{
    type Src<'a> = C::Result<'a>;
    type Dst<'a> = C::Result<'a>;

    type SrcOwned = C::Owned;
    type DstOwned = C::Owned;
}

}
