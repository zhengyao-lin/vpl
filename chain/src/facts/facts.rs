use vstd::prelude::*;
use vpl::*;
use parser::*;

use crate::error::*;

verus! {

pub trait Facts<Of: View> {
    /// Generate facts for the spec value
    spec fn spec_facts(t: Of::V) -> Option<Seq<SpecRule>>;

    /// Exec version of spec_facts
    fn facts(t: &Of, out: &mut VecDeep<Rule>) -> (res: Result<(), ValidationError>)
        ensures
            res.is_ok() ==> {
                &&& Self::spec_facts(t@) matches Some(facts)
                &&& out@ =~~= old(out)@ + facts
            };
}

/// Sequence two facts
pub struct Sequence<F1, F2>(F1, F2);

impl<T: View, F1: Facts<T>, F2: Facts<T>> Facts<T> for Sequence<F1, F2> {
    closed spec fn spec_facts(t: T::V) -> Option<Seq<SpecRule>> {
        if_let! {
            let Some(f1) = F1::spec_facts(t);
            let Some(f2) = F2::spec_facts(t);
            Some(f1 + f2)
        }
    }

    fn facts(t: &T, out: &mut VecDeep<Rule>) -> (res: Result<(), ValidationError>) {
        F1::facts(t, out)?;
        F2::facts(t, out)?;
        Ok(())
    }
}

/// Used for error handling in specs
#[allow(unused_macros)]
macro_rules! if_let {
    ($body:expr) => {
        ::builtin_macros::verus_proof_expr! { $body }
    };

    (let $pat:pat = $opt:expr; $(let $rest_pat:pat = $rest_opt:expr;)* $body:expr) => {
        #[allow(irrefutable_let_patterns)]
        if let $pat = ::builtin_macros::verus_proof_expr! { $opt } {
            if_let!($(let $rest_pat = $rest_opt;)* { $body })
        } else {
            None
        }
    };
}
pub(crate) use if_let;

/// Generate a type Sequence<f1, Sequence<f2, ...>>
#[allow(unused_macros)]
macro_rules! seq_facts {
    ($f:ty $(,)?) => { $f };
    ($f:ty $(, $rest:ty)+ $(,)?) => {
        Sequence<$f, seq_facts!($($rest),+)>
    };
}
pub(crate) use seq_facts;

}
