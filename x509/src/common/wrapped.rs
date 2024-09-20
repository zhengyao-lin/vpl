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

/// Wrap a non-parametric combinator in a new unit struct
/// e.g.
/// wrap_combinator! {
///     struct AlgorithmIdentifier: AlgorithmIdentifierInner =
///         Mapped {
///             inner: ASN1(ExplicitTag(TagValue {
///                 class: TagClass::Universal,
///                 form: TagForm::Constructed,
///                 num: 0x10,
///             }, (ASN1(ObjectIdentifier), Tail))),
///             mapper: AlgorithmIdentifierMapper,
///         }
/// }
///
/// TODO: Due to a Verus issue, everything here is unproved
/// NOTE: $inner_expr is used both in exec and spec mode
#[allow(unused_macros)]
macro_rules! wrap_combinator {
    (struct $name:ident: $inner_type:ty = $inner_expr:expr ;) => {
        wrap_combinator! {
            struct $name: $inner_type =>
                spec <<$inner_type as View>::V as SpecCombinator>::SpecResult,
                exec<'a> <$inner_type as Combinator>::Result<'a>,
                owned <$inner_type as Combinator>::Owned,
            = $inner_expr;
        }
    };

    // NOTE: use this alternative can reduce type checking time
    (struct $name:ident: $inner_type:ty =>
        spec $spec_result:ty,
        exec<$lt:lifetime> $result:ty,
        owned $owned:ty $(,)?
        = $inner_expr:expr ;) => {
        ::builtin_macros::verus! {
            #[derive(Debug, View)]
            pub struct $name;

            impl SpecCombinator for $name {
                type SpecResult = $spec_result;

                // $inner_expr.view().spec_parse(s)
                closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()>;

                #[verifier::external_body]
                proof fn spec_parse_wf(&self, s: Seq<u8>) {
                    // $inner_expr.view().spec_parse_wf(s)
                }

                // $inner_expr.view().spec_serialize(v)
                closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()>;
            }

            impl SecureSpecCombinator for $name {
                // $inner_type::spec_is_prefix_secure()
                closed spec fn spec_is_prefix_secure() -> bool;

                #[verifier::external_body]
                proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
                    // $inner_expr.view().theorem_serialize_parse_roundtrip(v)
                }

                #[verifier::external_body]
                proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
                    // $inner_expr.view().theorem_parse_serialize_roundtrip(buf)
                }

                #[verifier::external_body]
                proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
                    // $inner_expr.view().lemma_prefix_secure(s1, s2)
                }
            }

            impl Combinator for $name {
                type Result<$lt> = $result;
                type Owned =  $owned;

                /// TODO: using spec_algorithm_identifier() here
                /// would cause irrelevant proofs to fail
                closed spec fn spec_length(&self) -> Option<usize>;

                #[verifier::external_body]
                fn length(&self) -> Option<usize> {
                    $inner_expr.length()
                }

                #[verifier::external_body]
                fn exec_is_prefix_secure() -> bool {
                    $inner_type::exec_is_prefix_secure()
                }

                #[verifier::external_body]
                fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ()>) {
                    $inner_expr.parse(s)
                }

                #[verifier::external_body]
                fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, ()>) {
                    $inner_expr.serialize(v, data, pos)
                }
            }
        }
    };
}
pub(crate) use wrap_combinator;

}
