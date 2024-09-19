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

type SpecRDNInner = Seq<SpecAttributeTypeAndValueValue>;
type RDNInner<'a> = VecDeep<AttributeTypeAndValueValue<'a>>;
type RDNInnerOwned = VecDeep<AttributeTypeAndValueOwned>;

pub struct SpecRDNValue {
    attrs: Seq<SpecAttributeTypeAndValueValue>,
}

#[derive(Debug)]
pub struct RDNValue<'a> {
    attrs: Vec<AttributeTypeAndValueValue<'a>>,
}

pub struct RDNOwned {
    attrs: Vec<AttributeTypeAndValueOwned>,
}

impl<'a> View for RDNValue<'a> {
    type V = SpecRDNValue;

    closed spec fn view(&self) -> Self::V {
        SpecRDNValue {
            attrs: Seq::new(self.attrs.len() as nat, |i| self.attrs@[i]@),
        }
    }
}

impl View for RDNOwned {
    type V = SpecRDNValue;

    closed spec fn view(&self) -> Self::V {
        SpecRDNValue {
            attrs: Seq::new(self.attrs.len() as nat, |i| self.attrs@[i]@),
        }
    }
}

impl<'a> PolyfillClone for RDNValue<'a> {
    fn clone(&self) -> Self {
        RDNValue {
            attrs: clone_vec_inner(&self.attrs),
        }
    }
}

impl SpecFrom<SpecRDNValue> for SpecRDNInner {
    closed spec fn spec_from(s: SpecRDNValue) -> Self {
        s.attrs
    }
}

impl SpecFrom<SpecRDNInner> for SpecRDNValue {
    closed spec fn spec_from(s: SpecRDNInner) -> Self {
        SpecRDNValue {
            attrs: s,
        }
    }
}

impl<'a> From<RDNValue<'a>> for RDNInner<'a> {
    fn ex_from(s: RDNValue<'a>) -> Self {
        VecDeep::from_vec(s.attrs)
    }
}

impl<'a> From<RDNInner<'a>> for RDNValue<'a> {
    fn ex_from(s: RDNInner<'a>) -> Self {
        RDNValue {
            attrs: s.to_vec(),
        }
    }
}

impl From<RDNOwned> for RDNInnerOwned {
    fn ex_from(s: RDNOwned) -> Self {
        VecDeep::from_vec(s.attrs)
    }
}

impl From<RDNInnerOwned> for RDNOwned {
    fn ex_from(s: RDNInnerOwned) -> Self {
        RDNOwned {
            attrs: s.to_vec(),
        }
    }
}

#[derive(Debug, View)]
pub struct RDNMapper;

impl SpecIso for RDNMapper {
    type Src = SpecRDNInner;
    type Dst = SpecRDNValue;

    proof fn spec_iso(s: Self::Src) {}
    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl Iso for RDNMapper {
    type Src<'a> = RDNInner<'a>;
    type Dst<'a> = RDNValue<'a>;

    type SrcOwned = RDNInnerOwned;
    type DstOwned = RDNOwned;
}

}
