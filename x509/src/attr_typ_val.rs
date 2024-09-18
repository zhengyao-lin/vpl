use vstd::prelude::*;

use crate::asn1::*;
use crate::asn1::vest::*;

use crate::utils::*;
use crate::dir_string::*;

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
pub type AttributeTypeAndValueCombinator = Mapped<ASN1<ExplicitTag<(ASN1<ObjectIdentifier>, DirectoryStringCombinator)>>, AttributeTypeAndValueMapper>;

pub fn x509_attribute_type_and_value() -> AttributeTypeAndValueCombinator {
    Mapped {
        inner: ASN1(ExplicitTag(TagValue {
            class: TagClass::Universal,
            form: TagForm::Constructed,
            num: 0x10,
        }, (ASN1(ObjectIdentifier), x509_directory_string()))),
        mapper: AttributeTypeAndValueMapper,
    }
}

pub struct SpecAttributeTypeAndValue {
    pub typ: SpecObjectIdentifierValue,
    pub value: SpecDirectoryString,
}

#[derive(Debug)]
pub struct AttributeTypeAndValue<'a> {
    pub typ: ObjectIdentifierValue,
    pub value: DirectoryString<'a>,
}

pub struct AttributeTypeAndValueOwned {
    pub typ: ObjectIdentifierValueOwned,
    pub value: DirectoryStringOwned,
}

type SpecAttributeTypeAndValueInner = (SpecObjectIdentifierValue, SpecDirectoryString);
type AttributeTypeAndValueInner<'a> = (ObjectIdentifierValue, DirectoryString<'a>);
type AttributeTypeAndValueInnerOwned = (ObjectIdentifierValueOwned, DirectoryStringOwned);

impl<'a> PolyfillClone for AttributeTypeAndValue<'a> {
    fn clone(&self) -> Self {
        AttributeTypeAndValue {
            typ: PolyfillClone::clone(&self.typ),
            value: PolyfillClone::clone(&self.value),
        }
    }
}

impl<'a> View for AttributeTypeAndValue<'a> {
    type V = SpecAttributeTypeAndValue;

    closed spec fn view(&self) -> Self::V {
        SpecAttributeTypeAndValue {
            typ: self.typ@,
            value: self.value@,
        }
    }
}

impl View for AttributeTypeAndValueOwned {
    type V = SpecAttributeTypeAndValue;

    closed spec fn view(&self) -> Self::V {
        SpecAttributeTypeAndValue {
            typ: self.typ@,
            value: self.value@,
        }
    }
}

impl SpecFrom<SpecAttributeTypeAndValue> for SpecAttributeTypeAndValueInner {
    closed spec fn spec_from(s: SpecAttributeTypeAndValue) -> Self {
        (s.typ, s.value)
    }
}

impl SpecFrom<SpecAttributeTypeAndValueInner> for SpecAttributeTypeAndValue {
    closed spec fn spec_from(s: SpecAttributeTypeAndValueInner) -> Self {
        SpecAttributeTypeAndValue {
            typ: s.0,
            value: s.1,
        }
    }
}

impl<'a> From<AttributeTypeAndValue<'a>> for AttributeTypeAndValueInner<'a> {
    fn ex_from(s: AttributeTypeAndValue<'a>) -> Self {
        (s.typ, s.value)
    }
}

impl<'a> From<AttributeTypeAndValueInner<'a>> for AttributeTypeAndValue<'a> {
    fn ex_from(s: AttributeTypeAndValueInner<'a>) -> Self {
        AttributeTypeAndValue {
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
    type Dst = SpecAttributeTypeAndValue;

    proof fn spec_iso(s: Self::Src) {}
    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl Iso for AttributeTypeAndValueMapper {
    type Src<'a> = AttributeTypeAndValueInner<'a>;
    type Dst<'a> = AttributeTypeAndValue<'a>;

    type SrcOwned = AttributeTypeAndValueInnerOwned;
    type DstOwned = AttributeTypeAndValueOwned;
}

}
