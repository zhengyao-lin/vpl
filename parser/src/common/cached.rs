use polyfill::slice_take;
use vstd::prelude::*;
use super::*;

verus! {

/// Same behavior as T, but also returns the slice
/// consumed by T in the exec version
#[derive(View)]
pub struct Cached<T>(pub T);

#[derive(Debug, PolyfillClone)]
pub struct CachedValue<'a, T> {
    pub x: T,
    pub serialized: &'a [u8],
}

pub struct CachedValueOwned<T> {
    pub x: T,
    pub serialized: Vec<u8>,
}

/// View of CachedValue discards the serialization
impl<'a, T: View> View for CachedValue<'a, T> {
    type V = T::V;

    open spec fn view(&self) -> Self::V {
        self.x@
    }
}

impl<T: View> View for CachedValueOwned<T> {
    type V = T::V;

    open spec fn view(&self) -> Self::V {
        self.x@
    }
}

impl<T: SpecCombinator> SpecCombinator for Cached<T> {
    type SpecResult = T::SpecResult;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        self.0.spec_parse(s)
    }

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        self.0.spec_serialize(v)
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        self.0.spec_parse_wf(s)
    }
}

impl<T: SecureSpecCombinator> SecureSpecCombinator for Cached<T> {
    open spec fn is_prefix_secure() -> bool {
        T::is_prefix_secure()
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        self.0.lemma_prefix_secure(s1, s2)
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        self.0.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, s: Seq<u8>) {
        self.0.theorem_parse_serialize_roundtrip(s)
    }
}

impl<T: Combinator> Combinator for Cached<T> where
    T::V: SecureSpecCombinator<SpecResult = <T::Owned as View>::V>,
{
    type Result<'a> = CachedValue<'a, T::Result<'a>>;
    type Owned = CachedValueOwned<T::Owned>;

    open spec fn spec_length(&self) -> Option<usize> {
        self.0.spec_length()
    }

    fn length(&self) -> Option<usize> {
        self.0.length()
    }

    open spec fn parse_requires(&self) -> bool {
        self.0.parse_requires()
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        let (n, x) = self.0.parse(s)?;
        Ok((n, CachedValue { x, serialized: slice_take(s, n) }))
    }

    open spec fn serialize_requires(&self) -> bool {
        self.0.serialize_requires()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        self.0.serialize(v.x, data, pos)
    }
}

}
