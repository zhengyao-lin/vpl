use vstd::prelude::*;
use super::*;

verus! {

/// An Option type with "deep" View
#[derive(Debug, View, PolyfillClone, Structural, Eq, PartialEq)]
pub enum OptionDeep<T> {
    Some(T),
    None,
}

}
