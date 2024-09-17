use der::Sequence;
/// Implement PolyfillClone for some types

use vstd::prelude::*;

use super::vest::*;
use super::bounds::*;
use super::repeat::*;
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

impl<T: PolyfillCloneCombinator> PolyfillCloneCombinator for SequenceOf<T> where
    <T as View>::V: SecureSpecCombinator<SpecResult = <T::Owned as View>::V>,
    for<'a> <T as Combinator>::Result<'a>: PolyfillClone,
{
    fn clone(&self) -> Self {
        SequenceOf(self.0.clone())
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
