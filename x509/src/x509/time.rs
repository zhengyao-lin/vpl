use vstd::prelude::*;

use crate::asn1::*;
use crate::common::*;

verus! {

/// In X.509:
/// Time ::= CHOICE {
///     utcTime        UTCTime, // more common
///     generalTime    GeneralizedTime
/// }
///
/// TODO: The restrictions on UTCTime and GeneralizedTime are somewhat complicated,
/// so we use UTF8String as their placeholder for now
pub type TimeInner = Mapped<OrdChoice<ASN1<ImplicitTag<UTF8String>>, ASN1<ImplicitTag<UTF8String>>>, TimeMapper>;

wrap_combinator! {
    struct Time: TimeInner =>
        SpecTimeValue,
        TimeValue<'a>,
        TimeValueOwned
    =
        Mapped {
            inner: OrdChoice(
                // UTCTime, tag 0x17
                ASN1(ImplicitTag(TagValue {
                    class: TagClass::Universal,
                    form: TagForm::Primitive,
                    num: 0x17,
                }, UTF8String)),

                // GeneralizedTime, tag 0x18
                ASN1(ImplicitTag(TagValue {
                    class: TagClass::Universal,
                    form: TagForm::Primitive,
                    num: 0x18,
                }, UTF8String)),
            ),
            mapper: TimeMapper,
        };
}

#[derive(Debug, View, PolyfillClone)]
pub enum TimePoly<UT, GT> {
    UTCTime(UT),
    GeneralizedTime(GT),
}

pub type SpecTimeValue = TimePoly<SpecUTF8StringValue, SpecUTF8StringValue>;
pub type TimeValue<'a> = TimePoly<UTF8StringValue<'a>, UTF8StringValue<'a>>;
pub type TimeValueOwned = TimePoly<UTF8StringValueOwned, UTF8StringValueOwned>;

pub type TimeFrom<UT, GT> = Either<UT, GT>;

impl<UT, GT> SpecFrom<TimeFrom<UT, GT>> for TimePoly<UT, GT> {
    open spec fn spec_from(inner: TimeFrom<UT, GT>) -> Self {
        match inner {
            Either::Left(s) => TimePoly::UTCTime(s),
            Either::Right(s) => TimePoly::GeneralizedTime(s),
        }
    }
}

impl<UT, GT> SpecFrom<TimePoly<UT, GT>> for TimeFrom<UT, GT> {
    open spec fn spec_from(inner: TimePoly<UT, GT>) -> Self {
        match inner {
            TimePoly::UTCTime(s) => Either::Left(s),
            TimePoly::GeneralizedTime(s) => Either::Right(s),
        }
    }
}

impl<UT: View, GT: View> From<TimePoly<UT, GT>> for TimeFrom<UT, GT> {
    fn ex_from(inner: TimePoly<UT, GT>) -> Self {
        match inner {
            TimePoly::UTCTime(s) => Either::Left(s),
            TimePoly::GeneralizedTime(s) => Either::Right(s),
        }
    }
}

impl<UT: View, GT: View> From<TimeFrom<UT, GT>> for TimePoly<UT, GT> {
    fn ex_from(inner: TimeFrom<UT, GT>) -> Self {
        match inner {
            Either::Left(s) => TimePoly::UTCTime(s),
            Either::Right(s) => TimePoly::GeneralizedTime(s),
        }
    }
}

#[derive(Debug, View)]
pub struct TimeMapper;

impl SpecIso for TimeMapper {
    type Src = TimeFrom<SpecUTF8StringValue, SpecUTF8StringValue>;
    type Dst = TimePoly<SpecUTF8StringValue, SpecUTF8StringValue>;

    proof fn spec_iso(s: Self::Src) {}
    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl Iso for TimeMapper {
    type Src<'a> = TimeFrom<UTF8StringValue<'a>, UTF8StringValue<'a>>;
    type Dst<'a> = TimePoly<UTF8StringValue<'a>, UTF8StringValue<'a>>;

    type SrcOwned = TimeFrom<UTF8StringValueOwned, UTF8StringValueOwned>;
    type DstOwned = TimePoly<UTF8StringValueOwned, UTF8StringValueOwned>;
}

}
