use vstd::prelude::*;

use crate::asn1::*;
use crate::common::*;

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

#[derive(Debug, View, PolyfillClone)]
pub struct ValidityPoly<NB, NA> {
    pub not_before: NB,
    pub not_after: NA,
}

pub type SpecValidityValue = ValidityPoly<SpecTime, SpecTime>;
pub type ValidityValue<'a> = ValidityPoly<Time<'a>, Time<'a>>;
pub type ValidityOwned = ValidityPoly<TimeOwned, TimeOwned>;

type ValidityFrom<NB, NA> = (NB, NA);

impl<NB, NA> SpecFrom<ValidityPoly<NB, NA>> for ValidityFrom<NB, NA> {
    closed spec fn spec_from(s: ValidityPoly<NB, NA>) -> Self {
        (s.not_before, s.not_after)
    }
}

impl<NB, NA> SpecFrom<ValidityFrom<NB, NA>> for ValidityPoly<NB, NA> {
    closed spec fn spec_from(s: ValidityFrom<NB, NA>) -> Self {
        ValidityPoly {
            not_before: s.0,
            not_after: s.1,
        }
    }
}

impl<NB: View, NA: View> From<ValidityPoly<NB, NA>> for ValidityFrom<NB, NA> {
    fn ex_from(s: ValidityPoly<NB, NA>) -> Self {
        (s.not_before, s.not_after)
    }
}

impl<NB: View, NA: View> From<ValidityFrom<NB, NA>> for ValidityPoly<NB, NA> {
    fn ex_from(s: ValidityFrom<NB, NA>) -> Self {
        ValidityPoly {
            not_before: s.0,
            not_after: s.1,
        }
    }
}

#[derive(Debug, View)]
pub struct ValidityMapper;

impl SpecIso for ValidityMapper {
    type Src = ValidityFrom<SpecTime, SpecTime>;
    type Dst = ValidityPoly<SpecTime, SpecTime>;

    proof fn spec_iso(s: Self::Src) {}
    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl Iso for ValidityMapper {
    type Src<'a> = ValidityFrom<Time<'a>, Time<'a>>;
    type Dst<'a> = ValidityPoly<Time<'a>, Time<'a>>;

    type SrcOwned = ValidityFrom<TimeOwned, TimeOwned>;
    type DstOwned = ValidityPoly<TimeOwned, TimeOwned>;
}

}
