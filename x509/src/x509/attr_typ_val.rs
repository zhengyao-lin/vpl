use vstd::prelude::*;

use crate::asn1::*;
use crate::common::*;
use crate::utils::*;

use super::dir_string::*;

verus! {

/// AttributeTypeAndValue in X.509:
/// AttributeTypeAndValue ::= SEQUENCE {
///     type     AttributeType,
///     value    AttributeValue
/// }
///
/// AttributeType ::= OBJECT IDENTIFIER
/// AttributeValue ::= ANY DEFINED BY AttributeType
///
/// where "in general AttributeValue will be a DirectoryString" (4.1.2.4, RFC 2459)
pub type AttributeTypeAndValue = Mapped<ASN1<ExplicitTag<(ASN1<ObjectIdentifier>, DirectoryString)>>, AttributeTypeAndValueMapper>;

pub fn attribute_type_and_value() -> AttributeTypeAndValue {
    Mapped {
        inner: ASN1(ExplicitTag(TagValue {
            class: TagClass::Universal,
            form: TagForm::Constructed,
            num: 0x10,
        }, (ASN1(ObjectIdentifier), directory_string()))),
        mapper: AttributeTypeAndValueMapper,
    }
}

pub struct SpecAttributeTypeAndValueValue {
    pub typ: SpecObjectIdentifierValue,
    pub value: SpecDirectoryStringValue,
}

#[derive(Debug)]
pub struct AttributeTypeAndValueValue<'a> {
    pub typ: ObjectIdentifierValue,
    pub value: DirectoryStringValue<'a>,
}

pub struct AttributeTypeAndValueOwned {
    pub typ: ObjectIdentifierValueOwned,
    pub value: DirectoryStringOwned,
}

type SpecAttributeTypeAndValueInner = (SpecObjectIdentifierValue, SpecDirectoryStringValue);
type AttributeTypeAndValueInner<'a> = (ObjectIdentifierValue, DirectoryStringValue<'a>);
type AttributeTypeAndValueInnerOwned = (ObjectIdentifierValueOwned, DirectoryStringOwned);

impl<'a> PolyfillClone for AttributeTypeAndValueValue<'a> {
    fn clone(&self) -> Self {
        AttributeTypeAndValueValue {
            typ: PolyfillClone::clone(&self.typ),
            value: PolyfillClone::clone(&self.value),
        }
    }
}

impl<'a> View for AttributeTypeAndValueValue<'a> {
    type V = SpecAttributeTypeAndValueValue;

    closed spec fn view(&self) -> Self::V {
        SpecAttributeTypeAndValueValue {
            typ: self.typ@,
            value: self.value@,
        }
    }
}

impl View for AttributeTypeAndValueOwned {
    type V = SpecAttributeTypeAndValueValue;

    closed spec fn view(&self) -> Self::V {
        SpecAttributeTypeAndValueValue {
            typ: self.typ@,
            value: self.value@,
        }
    }
}

impl SpecFrom<SpecAttributeTypeAndValueValue> for SpecAttributeTypeAndValueInner {
    closed spec fn spec_from(s: SpecAttributeTypeAndValueValue) -> Self {
        (s.typ, s.value)
    }
}

impl SpecFrom<SpecAttributeTypeAndValueInner> for SpecAttributeTypeAndValueValue {
    closed spec fn spec_from(s: SpecAttributeTypeAndValueInner) -> Self {
        SpecAttributeTypeAndValueValue {
            typ: s.0,
            value: s.1,
        }
    }
}

impl<'a> From<AttributeTypeAndValueValue<'a>> for AttributeTypeAndValueInner<'a> {
    fn ex_from(s: AttributeTypeAndValueValue<'a>) -> Self {
        (s.typ, s.value)
    }
}

impl<'a> From<AttributeTypeAndValueInner<'a>> for AttributeTypeAndValueValue<'a> {
    fn ex_from(s: AttributeTypeAndValueInner<'a>) -> Self {
        AttributeTypeAndValueValue {
            typ: s.0,
            value: s.1,
        }
    }
}

impl From<AttributeTypeAndValueOwned> for AttributeTypeAndValueInnerOwned {
    fn ex_from(s: AttributeTypeAndValueOwned) -> Self {
        (s.typ, s.value)
    }
}

impl From<AttributeTypeAndValueInnerOwned> for AttributeTypeAndValueOwned {
    fn ex_from(s: AttributeTypeAndValueInnerOwned) -> Self {
        AttributeTypeAndValueOwned {
            typ: s.0,
            value: s.1,
        }
    }
}

#[derive(Debug)]
pub struct AttributeTypeAndValueMapper;
impl_trivial_view!(AttributeTypeAndValueMapper);
impl_trivial_poly_clone!(AttributeTypeAndValueMapper);

impl SpecIso for AttributeTypeAndValueMapper {
    type Src = SpecAttributeTypeAndValueInner;
    type Dst = SpecAttributeTypeAndValueValue;

    proof fn spec_iso(s: Self::Src) {}
    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl Iso for AttributeTypeAndValueMapper {
    type Src<'a> = AttributeTypeAndValueInner<'a>;
    type Dst<'a> = AttributeTypeAndValueValue<'a>;

    type SrcOwned = AttributeTypeAndValueInnerOwned;
    type DstOwned = AttributeTypeAndValueOwned;
}

}
