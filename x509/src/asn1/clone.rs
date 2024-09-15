/// Implement PolyfillClone for some types

use vstd::prelude::*;

use super::vest::*;
use super::bounds::*;
use super::integer::Integer;

verus! {

/// A temporary replacement Clone
pub trait PolyfillClone: View + Sized {
    spec fn spec_clone(&self) -> Self;

    fn clone(&self) -> (res: Self)
        ensures
            res == self.spec_clone(),
            res@ == self@;
}

impl PolyfillClone for UInt {
    open spec fn spec_clone(&self) -> Self {
        *self
    }

    fn clone(&self) -> Self {
        *self
    }
}

impl PolyfillClone for Int {
    open spec fn spec_clone(&self) -> Self {
        *self
    }

    fn clone(&self) -> Self {
        *self
    }
}

impl PolyfillClone for Integer {
    open spec fn spec_clone(&self) -> Self {
        *self
    }

    fn clone(&self) -> Self {
        Integer
    }
}

}
