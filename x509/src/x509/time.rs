use vstd::prelude::*;

use crate::asn1::*;
use crate::common::*;
use crate::utils::*;

verus! {

/// In X.509:
/// Time ::= CHOICE {
///     utcTime        UTCTime, // more common
///     generalTime    GeneralizedTime
/// }
///
/// TODO: The restrictions on UTCTime and GeneralizedTime are somewhat complicated,
/// so we use UTF8String as their placeholder for now
pub type TimeCombinator = Mapped<OrdChoice<ASN1<ImplicitTag<UTF8String>>, ASN1<ImplicitTag<UTF8String>>>, TimeMapper>;

pub fn time() -> TimeCombinator {
    Mapped {
        inner: OrdChoice::new(
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
    }
}

pub enum SpecTime {
    UTCTime(SpecUTF8StringValue),
    GeneralizedTime(SpecUTF8StringValue),
}

#[derive(Debug)]
pub enum Time<'a> {
    UTCTime(UTF8StringValue<'a>),
    GeneralizedTime(UTF8StringValue<'a>),
}

pub enum TimeOwned {
    UTCTime(UTF8StringValueOwned),
    GeneralizedTime(UTF8StringValueOwned),
}

type SpecTimeInner = Either<SpecUTF8StringValue, SpecUTF8StringValue>;
type TimeInner<'a> = Either<UTF8StringValue<'a>, UTF8StringValue<'a>>;
type TimeInnerOwned = Either<UTF8StringValueOwned, UTF8StringValueOwned>;

impl<'a> PolyfillClone for Time<'a> {
    fn clone(&self) -> Self {
        match self {
            Time::UTCTime(s) => Time::UTCTime(PolyfillClone::clone(s)),
            Time::GeneralizedTime(s) => Time::GeneralizedTime(PolyfillClone::clone(s)),
        }
    }
}

impl<'a> View for Time<'a> {
    type V = SpecTime;

    closed spec fn view(&self) -> Self::V {
        match self {
            Time::UTCTime(s) => SpecTime::UTCTime(s@),
            Time::GeneralizedTime(s) => SpecTime::GeneralizedTime(s@),
        }
    }
}

impl View for TimeOwned {
    type V = SpecTime;

    closed spec fn view(&self) -> Self::V {
        match self {
            TimeOwned::UTCTime(s) => SpecTime::UTCTime(s@),
            TimeOwned::GeneralizedTime(s) => SpecTime::GeneralizedTime(s@),
        }
    }
}

impl SpecFrom<SpecTimeInner> for SpecTime {
    open spec fn spec_from(inner: SpecTimeInner) -> Self {
        match inner {
            Either::Left(s) => SpecTime::UTCTime(s),
            Either::Right(s) => SpecTime::GeneralizedTime(s),
        }
    }
}

impl SpecFrom<SpecTime> for SpecTimeInner {
    open spec fn spec_from(inner: SpecTime) -> Self {
        match inner {
            SpecTime::UTCTime(s) => Either::Left(s),
            SpecTime::GeneralizedTime(s) => Either::Right(s),
        }
    }
}

impl<'a> From<TimeInner<'a>> for Time<'a> {
    fn ex_from(inner: TimeInner<'a>) -> Self {
        match inner {
            Either::Left(s) => Time::UTCTime(s),
            Either::Right(s) => Time::GeneralizedTime(s),
        }
    }
}

impl<'a> From<Time<'a>> for TimeInner<'a> {
    fn ex_from(inner: Time<'a>) -> Self {
        match inner {
            Time::UTCTime(s) => Either::Left(s),
            Time::GeneralizedTime(s) => Either::Right(s),
        }
    }
}

impl From<TimeInnerOwned> for TimeOwned {
    fn ex_from(inner: TimeInnerOwned) -> Self {
        match inner {
            Either::Left(s) => TimeOwned::UTCTime(s),
            Either::Right(s) => TimeOwned::GeneralizedTime(s),
        }
    }
}

impl From<TimeOwned> for TimeInnerOwned {
    fn ex_from(inner: TimeOwned) -> Self {
        match inner {
            TimeOwned::UTCTime(s) => Either::Left(s),
            TimeOwned::GeneralizedTime(s) => Either::Right(s),
        }
    }
}

#[derive(Debug)]
pub struct TimeMapper;
impl_trivial_view!(TimeMapper);
impl_trivial_poly_clone!(TimeMapper);

impl SpecIso for TimeMapper {
    type Src = SpecTimeInner;
    type Dst = SpecTime;

    proof fn spec_iso(s: Self::Src) {}
    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl Iso for TimeMapper {
    type Src<'a> = TimeInner<'a>;
    type Dst<'a> = Time<'a>;

    type SrcOwned = TimeInnerOwned;
    type DstOwned = TimeOwned;
}

}
