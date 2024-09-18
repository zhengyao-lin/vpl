use vstd::prelude::*;

verus! {

/// Trivial view implementation
#[allow(unused_macros)]
macro_rules! impl_trivial_view {
    ($name:ident) => {
        ::builtin_macros::verus! {
            impl View for $name {
                type V = Self;

                open spec fn view(&self) -> Self::V {
                    *self
                }
            }
        }
    };
}
pub(crate) use impl_trivial_view;

}
