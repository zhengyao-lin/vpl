/// TODO
///
/// Examples:
///
/// Need:
/// 1. Combinator term
/// 2. Combinator type
/// 3. Value type
///
/// What are the leaf combinators to support?
/// - Unit struct combinators derived from wrap_combinator!
/// - Tail?
/// - Dependent?
///
/// asn1_sequence! {
///     sequence Test<'a> {
///         a ObjectIdentifier: ObjectIdentifierValue,
///         b [1] implicit IA5String optional: OptionDeep<IA5String<'a>>,
///         c [2] explicit IA5String optional: OptionDeep<IA5String<'a>>,
///     }
/// }

use vstd::prelude::*;

use crate::asn1::*;
use crate::common::*;

verus! {

}
