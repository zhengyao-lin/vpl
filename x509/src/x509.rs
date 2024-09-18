use vstd::prelude::*;

use crate::asn1::*;
use crate::asn1::vest::*;

use crate::dir_string::*;

verus! {

// /// Name ::= RDNSequence
// /// RDNSequence ::= SEQUENCE OF RelativeDistinguishedName
// /// RelativeDistinguishedName ::= SET OF AttributeTypeAndValue
// pub struct Name {

// }

pub fn x509_name();
pub fn x509_rdn_sequence();
pub fn x509_relative_distinguished_name();

// pub struct AttributeTypeAndValue<'a> {
//     pub typ: ObjectIdentifierValue,
//     pub value: DirectoryString<'a>,
// }

/// AttributeTypeAndValue ::= SEQUENCE {
///     type     AttributeType,
///     value    AttributeValue
/// }
///
/// AttributeType ::= OBJECT IDENTIFIER
/// AttributeValue ::= ANY DEFINED BY AttributeType
pub fn x509_attribute_type_and_value() -> ASN1<ExplicitTag<(ASN1<ObjectIdentifier>, DirectoryStringCombinator)>> {
    ASN1(ExplicitTag(TagValue {
        class: TagClass::Universal,
        form: TagForm::Constructed,
        num: 0x10,
    }, (ASN1(ObjectIdentifier), x509_directory_string())))
}

}
