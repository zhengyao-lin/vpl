use vstd::prelude::*;

pub use paste::paste;

use crate::asn1::*;
use crate::common::*;

verus! {

/// Example:
/// asn1_sequence! {
///     sequence Test<'a> {
///         typ: ASN1<ObjectIdentifier> = ASN1(ObjectIdentifier),
///         value: DirectoryString = DirectoryString,
///     }
/// }
///
/// NOTE: all sub-combinators have to be prefix secure (for Pair to work)
/// NOTE: we have the restriction that an OrdChoice combinator cannot
/// be following an optional or default field.
#[allow(unused_macros)]
macro_rules! asn1_sequence {
    // This assumes the view of $field_combinator is also $field_combinator
    (
        seq $combinator_name:ident {
            $(
                $(#[$modifier:ident $(($modifier_arg:expr))?])? $field_name:ident : $field_combinator_type:ty = $field_combinator:expr
            ),*

            $(,)?
        }
    ) => {
        asn1_sequence! {
            seq $combinator_name {
                $($(#[$modifier $(($modifier_arg))?])? $field_name : $field_combinator_type = $field_combinator, spec $field_combinator),*
            }
        }
    };

    (
        seq $combinator_name:ident {
            $(
                $(#[$modifier:ident $(($modifier_arg:expr))?])? $field_name:ident : $field_combinator_type:ty = $field_combinator:expr, spec $spec_field_combinator:expr
            ),*

            $(,)?
        }
    ) => {
        paste! {
            ::builtin_macros::verus! {
                // Wrap the final combinator in a unit struct called $combinator_name
                wrap_combinator! {
                    pub struct $combinator_name: Mapped<LengthWrapped<
                            gen_inner_combinator_type!($(($($modifier $(($modifier_arg))?)?, $field_combinator_type));*)
                        >, [< internal_ $combinator_name >]::Mapper> =>
                        spec [< Spec $combinator_name Value >],
                        exec<'a> [< $combinator_name Value >]<'a>,
                        owned [< $combinator_name ValueOwned >],
                    = Mapped {
                            inner: LengthWrapped(gen_inner_combinator!($(($($modifier $(($modifier_arg))?)?, $field_combinator));*)),
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

                    // Add an indirection here since we can't put it inside the struct definition
                    $(
                        pub type [<FieldType_ $field_name>]<$field_name> = gen_field_poly_type!(($($modifier $(($modifier_arg))?)?, $field_name));
                    )*

                    // Mapper from the inner nested pair type to a struct
                    mapper! {
                        pub struct Mapper;

                        for <$($field_name),*>
                        from FromType where
                            type FromType<$($field_name),*> = gen_inner_combinator_poly_result_type!($(($($modifier $(($modifier_arg))?)?, $field_name));*);
                        to PolyType where
                            pub struct PolyType<$($field_name),*> {
                                $(pub $field_name: [<FieldType_ $field_name>]<$field_name>,)*
                            }

                        spec SpecValue with <$(<<$field_combinator_type as View>::V as SpecCombinator>::SpecResult),*>;
                        exec Value<'a> with <$(<$field_combinator_type as Combinator>::Result<'a>),*>;
                        owned ValueOwned with <$(<$field_combinator_type as Combinator>::Owned),*>;

                        forward(x) {
                            gen_forward_body!(x; $(($($modifier $(($modifier_arg))?)?, $field_name)),*);
                            PolyType { $($field_name),* }
                        } by {
                            assert(get_end_field!(x; $(($($modifier $(($modifier_arg))?)?, $field_name)),*) == EndValue);
                        }

                        backward(y) {
                            gen_backward_body!(y; $(($($modifier $(($modifier_arg))?)?, $field_name)),*)
                        }
                    }
                }
            }
        }
    };
}
pub(crate) use asn1_sequence;

/// gen_inner_combinator_type!((optional, type1); (, type2); (default(v), type3))
#[allow(unused_macros)]
macro_rules! gen_inner_combinator_type {
    () => { End };

    ((, $first:ty) $(; ($($modifier:ident $(($modifier_arg:expr))?)?, $rest:ty))*) => {
        Pair<$first, gen_inner_combinator_type!($(($($modifier $(($modifier_arg))?)?, $rest));*)>
    };

    ((optional, $first:ty) $(; ($($modifier:ident $(($modifier_arg:expr))?)?, $rest:ty))*) => {
        Optional<$first, gen_inner_combinator_type!($(($($modifier $(($modifier_arg))?)?, $rest));*)>
    };

    ((default($_:expr), $first:ty) $(; ($($modifier:ident $(($modifier_arg:expr))?)?, $rest:ty))*) => {
        Default<<$first as Combinator>::Owned, $first, gen_inner_combinator_type!($(($($modifier $(($modifier_arg))?)?, $rest));*)>
    };

    ((tail, $first:ty)) => {
        $first
    };
}
pub(crate) use gen_inner_combinator_type;

#[allow(unused_macros)]
macro_rules! gen_inner_combinator {
    () => { End };

    ((, $first:expr) $(; ($($modifier:ident $(($modifier_arg:expr))?)?, $rest:expr))*) => {
        Pair($first, gen_inner_combinator!($(($($modifier $(($modifier_arg))?)?, $rest));*))
    };

    ((optional, $first:expr) $(; ($($modifier:ident $(($modifier_arg:expr))?)?, $rest:expr))*) => {
        Optional($first, gen_inner_combinator!($(($($modifier $(($modifier_arg))?)?, $rest));*))
    };

    ((default($default:expr), $first:expr) $(; ($($modifier:ident $(($modifier_arg:expr))?)?, $rest:expr))*) => {
        Default($default, $first, gen_inner_combinator!($(($($modifier $(($modifier_arg))?)?, $rest));*))
    };

    ((tail, $first:expr)) => {
        $first
    };
}
pub(crate) use gen_inner_combinator;

#[allow(unused_macros)]
macro_rules! gen_inner_combinator_poly_result_type {
    () => { EndValue };

    ((, $first:ident) $(; ($($modifier:ident $(($modifier_arg:expr))?)?, $rest:ident))*) => {
        PairValue<$first, gen_inner_combinator_poly_result_type!($(($($modifier $(($modifier_arg))?)?, $rest));*)>
    };

    ((optional, $first:ident) $(; ($($modifier:ident $(($modifier_arg:expr))?)?, $rest:ident))*) => {
        PairValue<OptionDeep<$first>, gen_inner_combinator_poly_result_type!($(($($modifier $(($modifier_arg))?)?, $rest));*)>
    };

    ((default($_:expr), $first:ident) $(; ($($modifier:ident $(($modifier_arg:expr))?)?, $rest:ident))*) => {
        PairValue<$first, gen_inner_combinator_poly_result_type!($(($($modifier $(($modifier_arg))?)?, $rest));*)>
    };

    ((tail, $first:ident)) => {
        $first
    };
}
pub(crate) use gen_inner_combinator_poly_result_type;

#[allow(unused_macros)]
macro_rules! gen_forward_body {
    ($prev_sel:expr ;) => {};

    // Special case: if the last field is marked with tail, we use it directly without doing Pair(last combinator, End)
    ($prev_sel:expr ; (tail, $first:ident)) => {
        let $first = $prev_sel;
    };

    ($prev_sel:expr ; ($($modifier:ident $(($modifier_arg:expr))?)?, $first:ident) $(, ($($rest_modifier:ident $(($rest_modifier_arg:expr))?)?, $rest:ident))*) => {
        let $first = $prev_sel.0;
        gen_forward_body!($prev_sel.1 ; $(($($rest_modifier $(($rest_modifier_arg))?)?, $rest)),*)
    };
}
pub(crate) use gen_forward_body;

#[allow(unused_macros)]
macro_rules! get_end_field {
    ($prev_sel:expr ;) => {
        $prev_sel
    };

    // Special case: if the last field is marked with tail, we use it directly without doing Pair(last combinator, End)
    // No proof required for the forward direction
    ($prev_sel:expr ; (tail, $first:ident)) => {
        EndValue
    };

    ($prev_sel:expr ; ($($modifier:ident $(($modifier_arg:expr))?)?, $first:ident) $(, ($($rest_modifier:ident $(($rest_modifier_arg:expr))?)?, $rest:ident))*) => {
        get_end_field!($prev_sel.1 ; $(($($rest_modifier $(($rest_modifier_arg))?)?, $rest)),*)
    };
}
pub(crate) use get_end_field;

#[allow(unused_macros)]
macro_rules! gen_backward_body {
    ($src:expr ;) => {
        EndValue
    };

    ($src:expr ; (tail, $first:ident)) => {
        $src.$first
    };

    ($src:expr ; ($($modifier:ident $(($modifier_arg:expr))?)?, $first:ident) $(, ($($rest_modifier:ident $(($rest_modifier_arg:expr))?)?, $rest:ident))*) => {
        PairValue($src.$first, gen_backward_body!($src ; $(($($rest_modifier $(($rest_modifier_arg))?)?, $rest)),*))
    };
}
pub(crate) use gen_backward_body;

#[allow(unused_macros)]
macro_rules! gen_field_poly_type {
    ((, $field:ident)) => {
        $field
    };

    ((optional, $field:ident)) => {
        OptionDeep<$field>
    };

    ((default($_:expr), $field:ident)) => {
        $field
    };

    ((tail, $field:ident)) => {
        $field
    };
}
pub(crate) use gen_field_poly_type;

// #[allow(unused_macros)]
// macro_rules! continuation {
//     (
//         $vis:vis struct $name:ident $(;)? as
//         <$lt:lifetime> |$input:ident : $input_type:ty| -> $output_type:ty {

//         }
//     ) => {
//         $field
//     };
// }
// pub(crate) use continuation;

// /// Parse an optional boolean field ("critical") (default to bool)
// /// before the actual extension parameter
// #[derive(Debug, View)]
// pub struct ExtensionCont;

// impl ExtensionCont {
//     pub open spec fn spec_apply(i: SpecObjectIdentifierValue) -> <ExtensionCont as Continuation>::Output {
//         Default(false, spec_new_wrapped(ASN1(Boolean)), ExtensionParamCont::spec_apply(i))
//     }
// }

// impl Continuation for ExtensionCont {
//     type Input<'a> = ObjectIdentifierValue;
//     type Output = Default<bool, Wrapped<ASN1<Boolean>>, <ExtensionParamCont as Continuation>::Output>;

//     fn apply<'a>(&self, i: Self::Input<'a>) -> (o: Self::Output) {
//         Default(false, new_wrapped(ASN1(Boolean)), ExtensionParamCont.apply(i))
//     }

//     open spec fn requires<'a>(&self, i: Self::Input<'a>) -> bool {
//         true
//     }

//     open spec fn ensures<'a>(&self, i: Self::Input<'a>, o: Self::Output) -> bool {
//         o@ == Self::spec_apply(i@)
//     }
// }

}
