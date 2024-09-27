use vstd::prelude::*;

pub use paste::paste;

use crate::asn1::*;
use crate::common::*;

verus! {

#[allow(unused_macros)]
macro_rules! gen_inner_combinator_type {
    () => { End };

    ($first:ty $(, $rest:ty)*) => {
        Pair<$first, gen_inner_combinator_type!($($rest),*)>
    };
}
pub(crate) use gen_inner_combinator_type;

#[allow(unused_macros)]
macro_rules! gen_inner_combinator {
    () => { End };

    ($first:expr $(, $rest:expr)*) => {
        Pair($first, gen_inner_combinator!($($rest),*))
    };
}
pub(crate) use gen_inner_combinator;

#[allow(unused_macros)]
macro_rules! gen_inner_combinator_poly_result_type {
    () => { EndValue };

    ($first:ident $(, $rest:ident)*) => {
        PairValue<$first, gen_inner_combinator_poly_result_type!($($rest),*)>
    };
}
pub(crate) use gen_inner_combinator_poly_result_type;

#[allow(unused_macros)]
macro_rules! gen_forward_body {
    ($prev_sel:expr ;) => {};

    ($prev_sel:expr ; $first:ident $(, $rest:ident)*) => {
        let $first = $prev_sel.0;
        gen_forward_body!($prev_sel.1 ; $($rest),*)
    };
}
pub(crate) use gen_forward_body;

#[allow(unused_macros)]
macro_rules! gen_backward_body {
    ($src:expr ;) => {
        EndValue
    };

    ($src:expr ; $first:ident $(, $rest:ident)*) => {
        PairValue($src.$first, gen_backward_body!($src ; $($rest),*))
    };
}
pub(crate) use gen_backward_body;

// Get the last field of a nested pair type (which should be an EndValue in our case)
#[allow(unused_macros)]
macro_rules! get_end_field {
    ($src:expr ;) => {
        $src
    };

    ($src:expr ; $_:ident $(, $rest:ident)*) => {
        get_end_field!($src.1 ; $($rest),*)
    };
}
pub(crate) use get_end_field;

/// Example:
/// asn1_sequence! {
///     sequence Test<'a> {
///         typ: ASN1<ObjectIdentifier> = ASN1(ObjectIdentifier),
///         value: DirectoryString = DirectoryString,
///     }
/// }
///
/// NOTE: all sub-combinators have to be prefix secure (for Pair to work)
#[allow(unused_macros)]
macro_rules! asn1_sequence {
    (
        seq $combinator_name:ident {
            $(
                $field_name:ident : $field_combinator_type:ty = $field_combinator:expr
            ),*

            $(,)?
        }
    ) => {
        paste! {
            // Wrap the final combinator in a unit struct called $combinator_name
            wrap_combinator! {
                pub struct $combinator_name: Mapped<LengthWrapped<gen_inner_combinator_type!($($field_combinator_type),*)>, [< internal_ $combinator_name >]::Mapper> =>
                    spec [< Spec $combinator_name Value >],
                    exec<'a> [< $combinator_name Value >]<'a>,
                    owned [< $combinator_name ValueOwned >],
                = Mapped {
                        inner: LengthWrapped(gen_inner_combinator!($($field_combinator),*)),
                        mapper: [< internal_ $combinator_name >]::Mapper,
                    };
            }

            // Tag of SEQUENCE
            asn1_tagged!($combinator_name, TagValue {
                class: TagClass::Universal,
                form: TagForm::Constructed,
                num: 0x10,
            });

            // Declare the spec/normal/owned result types
            pub type [< Spec $combinator_name Value >] = [< internal_ $combinator_name >]::SpecValue;
            pub type [< $combinator_name Value >]<'a> = [< internal_ $combinator_name >]::Value<'a>;
            pub type [< $combinator_name ValueOwned >] = [< internal_ $combinator_name >]::ValueOwned;

            // Implement a mapper from nested pairs to a struct
            mod [< internal_ $combinator_name >] {
                // Since snake-case field names are directly used
                // as type parameters
                #![allow(non_camel_case_types)]
                #![allow(non_snake_case)]

                use super::*;

                // Mapper from the inner nested pair type to a struct
                mapper! {
                    pub struct Mapper;

                    for <$($field_name),*>
                    from FromType where
                        type FromType<$($field_name),*> = gen_inner_combinator_poly_result_type!($($field_name),*);
                    to PolyType where
                        pub struct PolyType<$($field_name),*> {
                            $(pub $field_name: $field_name),*
                        }

                    spec SpecValue with <$(<<$field_combinator_type as View>::V as SpecCombinator>::SpecResult),*>;
                    exec Value<'a> with <$(<$field_combinator_type as Combinator>::Result<'a>),*>;
                    owned ValueOwned with <$(<$field_combinator_type as Combinator>::Owned),*>;

                    forward(x) {
                        gen_forward_body!(x; $($field_name),*);
                        PolyType { $($field_name),* }
                    } by {
                        assert(get_end_field!(x; $($field_name),*) == EndValue);
                    }

                    backward(y) {
                        gen_backward_body!(y; $($field_name),*)
                    }
                }
            }
        }
    };
}
pub(crate) use asn1_sequence;

}
