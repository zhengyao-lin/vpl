use vstd::prelude::*;

use crate::asn1::*;
use crate::asn1::vest::*;

use crate::utils::*;
use crate::attr_typ_val::*;

verus! {

/// In X.509: RelativeDistinguishedName ::= SET OF AttributeTypeAndValue
/// TODO: support SET OF instead of using a sequence
pub type RelativeDistinguishedNameCombinator = Mapped<ASN1<ImplicitTag<SequenceOf<AttributeTypeAndValueCombinator>>>, RelativeDistinguishedNameMapper>;

pub fn x509_relative_distinguished_name() -> RelativeDistinguishedNameCombinator {
    Mapped {
        inner: ASN1(ImplicitTag(TagValue {
            class: TagClass::Universal,
            form: TagForm::Constructed,
            num: 0x11,
        }, SequenceOf(x509_attribute_type_and_value()))),
        mapper: RelativeDistinguishedNameMapper,
    }
}

type SpecRelativeDistinguishedNameInner = Seq<SpecAttributeTypeAndValue>;
type RelativeDistinguishedNameInner<'a> = RepeatResult<AttributeTypeAndValue<'a>>;
type RelativeDistinguishedNameInnerOwned = RepeatResultOwned<AttributeTypeAndValueOwned>;

pub struct SpecRelativeDistinguishedName {
    attrs: Seq<SpecAttributeTypeAndValue>,
}

#[derive(Debug)]
pub struct RelativeDistinguishedName<'a> {
    attrs: Vec<AttributeTypeAndValue<'a>>,
}

pub struct RelativeDistinguishedNameOwned {
    attrs: Vec<AttributeTypeAndValueOwned>,
}

impl<'a> View for RelativeDistinguishedName<'a> {
    type V = SpecRelativeDistinguishedName;

    closed spec fn view(&self) -> Self::V {
        SpecRelativeDistinguishedName {
            attrs: Seq::new(self.attrs.len() as nat, |i| self.attrs@[i]@),
        }
    }
}

impl View for RelativeDistinguishedNameOwned {
    type V = SpecRelativeDistinguishedName;

    closed spec fn view(&self) -> Self::V {
        SpecRelativeDistinguishedName {
            attrs: Seq::new(self.attrs.len() as nat, |i| self.attrs@[i]@),
        }
    }
}

impl<'a> PolyfillClone for RelativeDistinguishedName<'a> {
    fn clone(&self) -> Self {
        RelativeDistinguishedName {
            attrs: clone_vec_inner(&self.attrs),
        }
    }
}

impl SpecFrom<SpecRelativeDistinguishedName> for SpecRelativeDistinguishedNameInner {
    closed spec fn spec_from(s: SpecRelativeDistinguishedName) -> Self {
        s.attrs
    }
}

impl SpecFrom<SpecRelativeDistinguishedNameInner> for SpecRelativeDistinguishedName {
    closed spec fn spec_from(s: SpecRelativeDistinguishedNameInner) -> Self {
        SpecRelativeDistinguishedName {
            attrs: s,
        }
    }
}

impl<'a> From<RelativeDistinguishedName<'a>> for RelativeDistinguishedNameInner<'a> {
    fn ex_from(s: RelativeDistinguishedName<'a>) -> Self {
        RepeatResult(s.attrs)
    }
}

impl<'a> From<RelativeDistinguishedNameInner<'a>> for RelativeDistinguishedName<'a> {
    fn ex_from(s: RelativeDistinguishedNameInner<'a>) -> Self {
        RelativeDistinguishedName {
            attrs: s.0,
        }
    }
}

impl From<RelativeDistinguishedNameOwned> for RelativeDistinguishedNameInnerOwned {
    fn ex_from(s: RelativeDistinguishedNameOwned) -> Self {
        RepeatResultOwned(s.attrs)
    }
}

impl From<RelativeDistinguishedNameInnerOwned> for RelativeDistinguishedNameOwned {
    fn ex_from(s: RelativeDistinguishedNameInnerOwned) -> Self {
        RelativeDistinguishedNameOwned {
            attrs: s.0,
        }
    }
}

#[derive(Debug)]
pub struct RelativeDistinguishedNameMapper;
impl_trivial_view!(RelativeDistinguishedNameMapper);
impl_trivial_poly_clone!(RelativeDistinguishedNameMapper);

impl SpecIso for RelativeDistinguishedNameMapper {
    type Src = SpecRelativeDistinguishedNameInner;
    type Dst = SpecRelativeDistinguishedName;

    proof fn spec_iso(s: Self::Src) {}
    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl Iso for RelativeDistinguishedNameMapper {
    type Src<'a> = RelativeDistinguishedNameInner<'a>;
    type Dst<'a> = RelativeDistinguishedName<'a>;

    type SrcOwned = RelativeDistinguishedNameInnerOwned;
    type DstOwned = RelativeDistinguishedNameOwned;
}

}
