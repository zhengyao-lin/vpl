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

macro_rules! impl_polyfill_clone_for_base_combinator {
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

impl_polyfill_clone_for_base_combinator!(Tail);
impl_polyfill_clone_for_base_combinator!(Integer);
impl_polyfill_clone_for_base_combinator!(BitString);
impl_polyfill_clone_for_base_combinator!(IA5String);
impl_polyfill_clone_for_base_combinator!(OctetString);
impl_polyfill_clone_for_base_combinator!(ObjectIdentifier);
impl_polyfill_clone_for_base_combinator!(UTF8String);

impl<T1: PolyfillCloneCombinator, T2: PolyfillCloneCombinator> PolyfillCloneCombinator for (T1, T2) where
    <T1 as View>::V: SecureSpecCombinator<SpecResult = <T1::Owned as View>::V>,
    <T2 as View>::V: SecureSpecCombinator<SpecResult = <T2::Owned as View>::V>,
{
    fn clone(&self) -> Self {
        (self.0.clone(), self.1.clone())
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

/// Clone RepeatResult (a wrapper around Vec) by cloning each element
impl<'a, C: Combinator> PolyfillClone for RepeatResult<'a, C> where
    <C as View>::V: SecureSpecCombinator<SpecResult = <C::Owned as View>::V>,
    for<'b> <C as Combinator>::Result<'b>: PolyfillClone,
{
    /// Same as clone of Vec, but this is a "deep" copy
    fn clone(&self) -> Self {
        let mut cloned: Vec<<C as Combinator>::Result<'a>> = Vec::new();

        for i in 0..self.0.len()
            invariant
                cloned.len() == i,
                forall |j| 0 <= j < i ==> cloned[j]@ == #[trigger] self.0[j]@,
        {
            cloned.push(self.0[i].clone());
        }

        assert(RepeatResult::<C>(cloned)@ =~= self@);

        RepeatResult(cloned)
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
