use vstd::prelude::*;
use super::*;

verus! {

/// An Option type with "deep" View
#[derive(Debug, View, PolyfillClone, Structural, Eq, PartialEq)]
pub enum OptionDeep<T> {
    Some(T),
    None,
}

impl<T> OptionDeep<T> {
    pub open spec fn spec_unwrap_or(self, default: T) -> T {
        match self {
            OptionDeep::Some(t) => t,
            OptionDeep::None => default,
        }
    }

    #[verifier::when_used_as_spec(spec_unwrap_or)]
    pub fn unwrap_or(self, default: T) -> (res: T)
        ensures res == self.spec_unwrap_or(default)
    {
        match self {
            OptionDeep::Some(t) => t,
            OptionDeep::None => default,
        }
    }

    pub open spec fn spec_as_ref(&self) -> Option<&T> {
        match self {
            OptionDeep::Some(t) => Some(t),
            OptionDeep::None => None,
        }
    }

    #[verifier::when_used_as_spec(spec_as_ref)]
    pub fn as_ref(&self) -> (res: Option<&T>)
        ensures res == self.spec_as_ref()
    {
        match self {
            OptionDeep::Some(t) => Some(t),
            OptionDeep::None => None,
        }
    }

    pub open spec fn spec_from_opt(opt: Option<T>) -> Self {
        match opt {
            Some(t) => OptionDeep::Some(t),
            None => OptionDeep::None,
        }
    }

    #[verifier::when_used_as_spec(spec_from_opt)]
    pub fn from_opt(opt: Option<T>) -> Self {
        match opt {
            Some(t) => OptionDeep::Some(t),
            None => OptionDeep::None,
        }
    }
}

}
