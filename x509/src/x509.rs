use vstd::prelude::*;

use crate::asn1::*;
use crate::asn1::vest::*;

verus! {

pub fn x509_name();
pub fn x509_rdn_sequence();
pub fn x509_relative_distinguished_name();

// pub struct AttributeTypeAndValue<'a> {
//     pub typ: ObjectIdentifierValue,
//     pub value: AttributeValue<'a>,
// }

// pub enum AttributeValue<'a> {
//     CommonName(String),
//     OrganizationName(String),
//     Other(&'a [u8]),
// }

/// AttributeTypeAndValue ::= SEQUENCE {
///     type     AttributeType,
///     value    AttributeValue
/// }
///
/// AttributeType ::= OBJECT IDENTIFIER
/// AttributeValue ::= ANY DEFINED BY AttributeType
pub fn x509_attribute_type_and_value() {
    ASN1(ExplicitTag(TagValue {
        class: TagClass::Universal,
        form: TagForm::Constructed,
        num: 0x10,
    }, (ASN1(ObjectIdentifier), Tail)));
}

}
