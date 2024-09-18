use der::Sequence;
/// Implement PolyfillClone for some types

use vstd::prelude::*;

use super::vest::*;
use super::bounds::*;
use super::repeat::*;
use super::integer::Integer;
use super::*;

verus! {

/// A temporary replacement Clone
pub trait PolyfillClone: View + Sized {
    fn clone(&self) -> (res: Self)
        ensures
            res@ == self@;
}

/// A property of some type that are both PolyfillClone and Combinator
/// cloning should preserve parse_requires() and serialize_requires()
pub trait PolyfillCloneCombinator: View + Sized + Combinator where
    <Self as View>::V: SecureSpecCombinator<SpecResult = <Self::Owned as View>::V>,
{
    fn clone(&self) -> (res: Self)
        ensures
            res@ == self@,
            res.parse_requires() == self.parse_requires(),
            res.serialize_requires() == self.serialize_requires();
}

impl PolyfillClone for UInt {
    fn clone(&self) -> Self {
        *self
    }
}

impl PolyfillClone for Int {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a> PolyfillClone for &'a str {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, T> PolyfillClone for &'a [T] {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: Copy> PolyfillClone for Vec<T>
{
    fn clone(&self) -> Self {
        let mut cloned: Vec<T> = Vec::new();

        for i in 0..self.len()
            invariant
                cloned.len() == i,
                forall |j| 0 <= j < i ==> #[trigger] cloned[j] == self[j],
        {
            cloned.push(self[i]);
        }

        assert(cloned@ =~= self@);

        cloned
    }
}

impl<T1: PolyfillClone, T2: PolyfillClone> PolyfillClone for (T1, T2) {
    fn clone(&self) -> Self {
        (self.0.clone(), self.1.clone())
    }
}

impl<T1: PolyfillClone, T2: PolyfillClone> PolyfillClone for Either<T1, T2> {
    fn clone(&self) -> Self {
        match self {
            Either::Left(v) => Either::Left(v.clone()),
            Either::Right(v) => Either::Right(v.clone()),
        }
    }
}

#[allow(unused_macros)]
macro_rules! impl_trivial_poly_clone_combinator {
    ($t:ty) => {
        ::builtin_macros::verus! {
            impl PolyfillCloneCombinator for $t {
                fn clone(&self) -> Self {
                    $t
                }
            }
        }
    };
}
pub(crate) use impl_trivial_poly_clone_combinator;

#[allow(unused_macros)]
macro_rules! impl_trivial_poly_clone {
    ($t:ty) => {
        ::builtin_macros::verus! {
            impl PolyfillClone for $t {
                fn clone(&self) -> Self {
                    $t
                }
            }
        }
    };
}
pub(crate) use impl_trivial_poly_clone;

impl_trivial_poly_clone_combinator!(Tail);
impl_trivial_poly_clone_combinator!(Integer);
impl_trivial_poly_clone_combinator!(BitString);
impl_trivial_poly_clone_combinator!(IA5String);
impl_trivial_poly_clone_combinator!(OctetString);
impl_trivial_poly_clone_combinator!(ObjectIdentifier);
impl_trivial_poly_clone_combinator!(UTF8String);
impl_trivial_poly_clone_combinator!(PrintableString);

impl<T1: PolyfillCloneCombinator, T2: PolyfillCloneCombinator> PolyfillCloneCombinator for (T1, T2) where
    <T1 as View>::V: SecureSpecCombinator<SpecResult = <T1::Owned as View>::V>,
    <T2 as View>::V: SecureSpecCombinator<SpecResult = <T2::Owned as View>::V>,
{
    fn clone(&self) -> Self {
        (self.0.clone(), self.1.clone())
    }
}

impl<T1: PolyfillCloneCombinator, T2: PolyfillCloneCombinator> PolyfillCloneCombinator for OrdChoice<T1, T2> where
    <T1 as View>::V: SecureSpecCombinator<SpecResult = <T1::Owned as View>::V>,
    <T2 as View>::V: SecureSpecCombinator<SpecResult = <T2::Owned as View>::V>,
    <T2 as View>::V: SpecDisjointFrom<T1::V>,
    T2: DisjointFrom<T1>,
{
    fn clone(&self) -> Self {
        OrdChoice(self.0.clone(), self.1.clone())
    }
}

impl<Inner: PolyfillCloneCombinator, M: PolyfillClone> PolyfillCloneCombinator for Mapped<Inner, M> where
    <Inner as View>::V: SecureSpecCombinator<SpecResult = <Inner::Owned as View>::V>,

    for <'a> M: Iso<Src<'a> = Inner::Result<'a>, SrcOwned = Inner::Owned>,
    for <'a>Inner::Result<'a>: From<M::Dst<'a>> + View,
    for <'a>M::Dst<'a>: From<Inner::Result<'a>> + View,

    M::V: SpecIso<Src = <Inner::Owned as View>::V, Dst = <M::DstOwned as View>::V>,
    <Inner::Owned as View>::V: SpecFrom<<M::DstOwned as View>::V>,
    <M::DstOwned as View>::V: SpecFrom<<Inner::Owned as View>::V>,
{
    fn clone(&self) -> Self {
        Mapped { inner: self.inner.clone(), mapper: self.mapper.clone() }
    }
}

impl<T: PolyfillCloneCombinator> PolyfillCloneCombinator for ImplicitTag<T> where
    <T as View>::V: SecureSpecCombinator<SpecResult = <T::Owned as View>::V>,
    <T as View>::V: ASN1Tagged,
    T: ViewWithASN1Tagged,
{
    fn clone(&self) -> Self {
        ImplicitTag(self.0.clone(), self.1.clone())
    }
}

impl<T: PolyfillCloneCombinator> PolyfillCloneCombinator for ExplicitTag<T> where
    <T as View>::V: SecureSpecCombinator<SpecResult = <T::Owned as View>::V>,
    for<'a> <T as Combinator>::Result<'a>: PolyfillClone,
{
    fn clone(&self) -> Self {
        ExplicitTag(self.0.clone(), self.1.clone())
    }
}

impl<T: PolyfillCloneCombinator> PolyfillCloneCombinator for ASN1<T> where
    <T as View>::V: SecureSpecCombinator<SpecResult = <T::Owned as View>::V>,
    <T as View>::V: ASN1Tagged,
    T: ViewWithASN1Tagged,
{
    fn clone(&self) -> Self {
        ASN1(self.0.clone())
    }
}

pub open spec fn vec_deep_view<T: View>(v: &Vec<T>) -> Seq<T::V>
{
    Seq::new(v.len() as nat, |i: int| v@[i]@)
}

/// Clone each element of Vec
pub fn clone_vec_inner<T: PolyfillClone>(v: &Vec<T>) -> (res: Vec<T>)
    ensures vec_deep_view(&res) =~= vec_deep_view(v)
{
    let mut cloned: Vec<T> = Vec::new();

    for i in 0..v.len()
        invariant
            cloned.len() == i,
            forall |j| 0 <= j < i ==> cloned[j]@ == #[trigger] v[j]@,
    {
        cloned.push(v[i].clone());
    }

    cloned
}

/// Clone RepeatResult (a wrapper around Vec) by cloning each element
impl<T: PolyfillClone> PolyfillClone for RepeatResult<T> where
{
    /// Same as clone of Vec, but this is a "deep" copy
    fn clone(&self) -> Self {
        RepeatResult(clone_vec_inner(&self.0))
    }
}

impl<C: PolyfillCloneCombinator> PolyfillCloneCombinator for Repeat<C> where
    <C as View>::V: SecureSpecCombinator<SpecResult = <C::Owned as View>::V>,
{
    fn clone(&self) -> Self {
        Repeat(self.0.clone())
    }
}

}
