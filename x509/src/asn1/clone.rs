/// Implement PolyfillClone for some types

use vstd::prelude::*;

use super::vest::*;
use super::bounds::*;
use super::*;

verus! {

/// A temporary replacement Clone
pub trait PolyfillClone: View + Sized {
    spec fn spec_clone(&self) -> Self;

    fn clone(&self) -> (res: Self)
        ensures
            res == self.spec_clone(),
            res@ == self@;

    proof fn lemma_spec_clone(&self)
        ensures self.spec_clone()@ == self@;
}

impl PolyfillClone for UInt {
    open spec fn spec_clone(&self) -> Self {
        *self
    }

    fn clone(&self) -> Self {
        *self
    }

    proof fn lemma_spec_clone(&self) {}
}

impl PolyfillClone for Int {
    open spec fn spec_clone(&self) -> Self {
        *self
    }

    fn clone(&self) -> Self {
        *self
    }

    proof fn lemma_spec_clone(&self) {}
}

macro_rules! impl_polyfill_clone_for_base_combinator {
    ($t:ty) => {
        ::builtin_macros::verus! {
            impl PolyfillClone for $t {
                open spec fn spec_clone(&self) -> Self {
                    *self
                }

                fn clone(&self) -> Self {
                    $t
                }

                proof fn lemma_spec_clone(&self) {}
            }
        }
    };
}

impl_polyfill_clone_for_base_combinator!(super::integer::Integer);
impl_polyfill_clone_for_base_combinator!(BitString);
impl_polyfill_clone_for_base_combinator!(IA5String);
impl_polyfill_clone_for_base_combinator!(OctetString);
impl_polyfill_clone_for_base_combinator!(ObjectIdentifier);
impl_polyfill_clone_for_base_combinator!(UTF8String);

impl<T: PolyfillClone> PolyfillClone for ASN1<T> {
    open spec fn spec_clone(&self) -> Self {
        ASN1(self.0.spec_clone())
    }

    fn clone(&self) -> Self {
        ASN1(self.0.clone())
    }

    proof fn lemma_spec_clone(&self) {
        self.0.lemma_spec_clone();
    }
}

}
