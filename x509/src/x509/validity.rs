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
pub type ValidityCombinator = Mapped<ASN1<ExplicitTag<(TimeCombinator, TimeCombinator)>>, ValidityMapper>;

pub fn x509_validity() -> ValidityCombinator {
    Mapped {
        inner: ASN1(ExplicitTag(TagValue {
            class: TagClass::Universal,
            form: TagForm::Constructed,
            num: 0x10,
        }, (x509_time(), x509_time()))),
        mapper: ValidityMapper,
    }
}

pub struct SpecValidity {
    pub not_before: SpecTime,
    pub not_after: SpecTime,
}

#[derive(Debug)]
pub struct Validity<'a> {
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

impl<'a> PolyfillClone for Validity<'a> {
    fn clone(&self) -> Self {
        Validity {
            not_before: PolyfillClone::clone(&self.not_before),
            not_after: PolyfillClone::clone(&self.not_after),
        }
    }
}

impl<'a> View for Validity<'a> {
    type V = SpecValidity;

    closed spec fn view(&self) -> Self::V {
        SpecValidity {
            not_before: self.not_before@,
            not_after: self.not_after@,
        }
    }
}

impl View for ValidityOwned {
    type V = SpecValidity;

    closed spec fn view(&self) -> Self::V {
        SpecValidity {
            not_before: self.not_before@,
            not_after: self.not_after@,
        }
    }
}

impl SpecFrom<SpecValidity> for SpecValidityInner {
    closed spec fn spec_from(s: SpecValidity) -> Self {
        (s.not_before, s.not_after)
    }
}

impl SpecFrom<SpecValidityInner> for SpecValidity {
    closed spec fn spec_from(s: SpecValidityInner) -> Self {
        SpecValidity {
            not_before: s.0,
            not_after: s.1,
        }
    }
}

impl<'a> From<Validity<'a>> for ValidityInner<'a> {
    fn ex_from(s: Validity<'a>) -> Self {
        (s.not_before, s.not_after)
    }
}

impl<'a> From<ValidityInner<'a>> for Validity<'a> {
    fn ex_from(s: ValidityInner<'a>) -> Self {
        Validity {
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
impl_trivial_poly_clone!(ValidityMapper);

impl SpecIso for ValidityMapper {
    type Src = SpecValidityInner;
    type Dst = SpecValidity;

    proof fn spec_iso(s: Self::Src) {}
    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl Iso for ValidityMapper {
    type Src<'a> = ValidityInner<'a>;
    type Dst<'a> = Validity<'a>;

    type SrcOwned = ValidityInnerOwned;
    type DstOwned = ValidityOwned;
}

}
