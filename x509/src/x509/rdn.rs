use vstd::prelude::*;

use crate::asn1::*;
use crate::common::*;

use super::attr_typ_val::*;

verus! {

/// In X.509: RelativeDistinguishedName ::= SET OF AttributeTypeAndValue
/// TODO: support SET OF instead of using a sequence
pub type RDN = Mapped<ASN1<ImplicitTag<SequenceOf<AttributeTypeAndValue>>>, RDNMapper>;

pub fn rdn() -> RDN {
    Mapped {
        inner: ASN1(ImplicitTag(TagValue {
            class: TagClass::Universal,
            form: TagForm::Constructed,
            num: 0x11,
        }, SequenceOf(attribute_type_and_value()))),
        mapper: RDNMapper,
    }
}

#[derive(Debug, View, PolyfillClone)]
pub struct RDNPoly<Attrs> {
    pub attrs: Attrs,
}

pub type SpecRDNValue = RDNPoly<Seq<SpecAttributeTypeAndValueValue>>;
pub type RDNValue<'a> = RDNPoly<VecDeep<AttributeTypeAndValueValue<'a>>>;
pub type RDNOwned = RDNPoly<VecDeep<AttributeTypeAndValueOwned>>;

type RDNFrom<T> = T;

impl<T> SpecFrom<RDNPoly<Seq<T>>> for RDNFrom<Seq<T>> {
    closed spec fn spec_from(s: RDNPoly<Seq<T>>) -> Self {
        s.attrs
    }
}

impl<T> SpecFrom<RDNFrom<T>> for RDNPoly<T> {
    closed spec fn spec_from(s: RDNFrom<T>) -> Self {
        RDNPoly {
            attrs: s,
        }
    }
}

impl<T: View> From<RDNPoly<VecDeep<T>>> for RDNFrom<VecDeep<T>> {
    fn ex_from(s: RDNPoly<VecDeep<T>>) -> Self {
        s.attrs
    }
}

impl<T: View> From<RDNFrom<T>> for RDNPoly<T> {
    fn ex_from(s: RDNFrom<T>) -> Self {
        RDNPoly {
            attrs: s,
        }
    }
}

#[derive(Debug, View)]
pub struct RDNMapper;

impl SpecIso for RDNMapper {
    type Src = RDNFrom<Seq<SpecAttributeTypeAndValueValue>>;
    type Dst = RDNPoly<Seq<SpecAttributeTypeAndValueValue>>;

    proof fn spec_iso(s: Self::Src) {}
    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl Iso for RDNMapper {
    type Src<'a> = RDNFrom<VecDeep<AttributeTypeAndValueValue<'a>>>;
    type Dst<'a> = RDNPoly<VecDeep<AttributeTypeAndValueValue<'a>>>;

    type SrcOwned = RDNFrom<VecDeep<AttributeTypeAndValueOwned>>;
    type DstOwned = RDNPoly<VecDeep<AttributeTypeAndValueOwned>>;
}

}
