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
pub type ValidityInner = Mapped<LengthWrapped<(Time, Time)>, ValidityMapper>;

wrap_combinator! {
    struct Validity: ValidityInner =>
        SpecValidityValue,
        ValidityValue<'a>,
        ValidityOwned
    =
        Mapped {
            inner: LengthWrapped((Time, Time)),
            mapper: ValidityMapper,
        };
}

asn1_tagged!(Validity, TagValue {
    class: TagClass::Universal,
    form: TagForm::Constructed,
    num: 0x10,
});

#[derive(Debug, View, PolyfillClone)]
pub struct ValidityPoly<NB, NA> {
    pub not_before: NB,
    pub not_after: NA,
}

pub type SpecValidityValue = ValidityPoly<SpecTimeValue, SpecTimeValue>;
pub type ValidityValue<'a> = ValidityPoly<TimeValue<'a>, TimeValue<'a>>;
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
    type Src = ValidityFrom<SpecTimeValue, SpecTimeValue>;
    type Dst = ValidityPoly<SpecTimeValue, SpecTimeValue>;

    proof fn spec_iso(s: Self::Src) {}
    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl Iso for ValidityMapper {
    type Src<'a> = ValidityFrom<TimeValue<'a>, TimeValue<'a>>;
    type Dst<'a> = ValidityPoly<TimeValue<'a>, TimeValue<'a>>;

    type SrcOwned = ValidityFrom<TimeOwned, TimeOwned>;
    type DstOwned = ValidityPoly<TimeOwned, TimeOwned>;
}

}
