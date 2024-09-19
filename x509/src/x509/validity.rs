use vstd::prelude::*;

use crate::asn1::*;
use crate::common::*;
use crate::utils::*;

use super::time::*;

verus! {

/// In X.509:
/// Validity ::= SEQUENCE {
///     notBefore      Time,
///     notAfter       Time,
/// }
pub type Validity = Mapped<ASN1<ExplicitTag<(TimeCombinator, TimeCombinator)>>, ValidityMapper>;

pub fn validity() -> Validity {
    Mapped {
        inner: ASN1(ExplicitTag(TagValue {
            class: TagClass::Universal,
            form: TagForm::Constructed,
            num: 0x10,
        }, (time(), time()))),
        mapper: ValidityMapper,
    }
}

pub struct SpecValidityValue {
    pub not_before: SpecTime,
    pub not_after: SpecTime,
}

#[derive(Debug)]
pub struct ValidityValue<'a> {
    pub not_before: Time<'a>,
    pub not_after: Time<'a>,
}

pub struct ValidityOwned {
    pub not_before: TimeOwned,
    pub not_after: TimeOwned,
}

type SpecValidityInner = (SpecTime, SpecTime);
type ValidityInner<'a> = (Time<'a>, Time<'a>);
type ValidityInnerOwned = (TimeOwned, TimeOwned);

impl<'a> PolyfillClone for ValidityValue<'a> {
    fn clone(&self) -> Self {
        ValidityValue {
            not_before: PolyfillClone::clone(&self.not_before),
            not_after: PolyfillClone::clone(&self.not_after),
        }
    }
}

impl<'a> View for ValidityValue<'a> {
    type V = SpecValidityValue;

    closed spec fn view(&self) -> Self::V {
        SpecValidityValue {
            not_before: self.not_before@,
            not_after: self.not_after@,
        }
    }
}

impl View for ValidityOwned {
    type V = SpecValidityValue;

    closed spec fn view(&self) -> Self::V {
        SpecValidityValue {
            not_before: self.not_before@,
            not_after: self.not_after@,
        }
    }
}

impl SpecFrom<SpecValidityValue> for SpecValidityInner {
    closed spec fn spec_from(s: SpecValidityValue) -> Self {
        (s.not_before, s.not_after)
    }
}

impl SpecFrom<SpecValidityInner> for SpecValidityValue {
    closed spec fn spec_from(s: SpecValidityInner) -> Self {
        SpecValidityValue {
            not_before: s.0,
            not_after: s.1,
        }
    }
}

impl<'a> From<ValidityValue<'a>> for ValidityInner<'a> {
    fn ex_from(s: ValidityValue<'a>) -> Self {
        (s.not_before, s.not_after)
    }
}

impl<'a> From<ValidityInner<'a>> for ValidityValue<'a> {
    fn ex_from(s: ValidityInner<'a>) -> Self {
        ValidityValue {
            not_before: s.0,
            not_after: s.1,
        }
    }
}

impl From<ValidityOwned> for ValidityInnerOwned {
    fn ex_from(s: ValidityOwned) -> Self {
        (s.not_before, s.not_after)
    }
}

impl From<ValidityInnerOwned> for ValidityOwned {
    fn ex_from(s: ValidityInnerOwned) -> Self {
        ValidityOwned {
            not_before: s.0,
            not_after: s.1,
        }
    }
}

#[derive(Debug)]
pub struct ValidityMapper;
impl_trivial_view!(ValidityMapper);

impl SpecIso for ValidityMapper {
    type Src = SpecValidityInner;
    type Dst = SpecValidityValue;

    proof fn spec_iso(s: Self::Src) {}
    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl Iso for ValidityMapper {
    type Src<'a> = ValidityInner<'a>;
    type Dst<'a> = ValidityValue<'a>;

    type SrcOwned = ValidityInnerOwned;
    type DstOwned = ValidityOwned;
}

}
