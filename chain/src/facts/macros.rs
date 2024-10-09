#[allow(unused_macros)]
macro_rules! count_args {
    () => { 0 };
    ($x:expr $(, $rest:expr)*) => { 1 + count_args!($($rest),*) };
}
pub(crate) use count_args;

#[allow(unused_macros)]
macro_rules! spec_app {
    ($name:expr $(, $args:expr)* $(,)?) => {
        ::builtin_macros::verus_proof_expr! {
            ::vpl::SpecTerm::App(
                ::vpl::SpecFnName::User($name.view(), count_args!($($args),*) as int),
                seq![$($args),*],
            )
        }
    };
}
pub(crate) use spec_app;

#[allow(unused_macros)]
macro_rules! spec_fact {
    ($name:expr $(, $args:expr)* $(,)?) => {
        ::builtin_macros::verus_proof_expr! {
            ::vpl::SpecRule {
                head: spec_app!($name $(, $args)*),
                body: seq![],
            }
        }
    }
}
pub(crate) use spec_fact;

/// String literal as a SpecTerm
#[allow(unused_macros)]
macro_rules! spec_str {
    ($x:expr) => {
        ::builtin_macros::verus_proof_expr! {
            ::vpl::SpecTerm::Literal(::vpl::SpecLiteral::String($x))
        }
    };
}
pub(crate) use spec_str;

/// Atom literal as a SpecTerm
#[allow(unused_macros)]
macro_rules! spec_atom {
    ($x:expr) => {
        ::builtin_macros::verus_proof_expr! {
            ::vpl::SpecTerm::Literal(::vpl::SpecLiteral::Atom($x))
        }
    };
}
pub(crate) use spec_atom;

/// String literal as a SpecTerm
#[allow(unused_macros)]
macro_rules! spec_int {
    ($x:expr) => {
        ::builtin_macros::verus_proof_expr! {
            ::vpl::SpecTerm::Literal(::vpl::SpecLiteral::Int($x))
        }
    };
}
pub(crate) use spec_int;

/// Atom literal as a SpecTerm
#[allow(unused_macros)]
macro_rules! spec_bool {
    ($x:expr) => {
        ::builtin_macros::verus_proof_expr! {
            ::vpl::SpecTerm::Literal(::vpl::SpecLiteral::Atom((if $x { "true" } else { "false" }).view()))
        }
    };
}
pub(crate) use spec_bool;
