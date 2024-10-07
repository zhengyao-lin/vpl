use vstd::prelude::*;

use crate::asn1::*;
use crate::asn1::Boolean;
use crate::asn1::Integer;

use crate::common::*;
use super::macros::*;

verus! {

// RFC 2459, 4.2.1.1
asn1_sequence! {
    seq AuthorityKeyIdentifier {
        #[optional] key_id: ASN1<ImplicitTag<OctetString>> = ASN1(ImplicitTag(tag_of!(IMPLICIT 0), OctetString)),
        // TODO: Parsing of GeneralNames is not implemented yet
        #[optional] auth_cert_issuer: placeholder_type!() = placeholder!(EXPLICIT 1),
        #[optional] auth_cert_serial: ASN1<ImplicitTag<BigInt>> = ASN1(ImplicitTag(tag_of!(IMPLICIT 2), BigInt)),
    }
}

// BasicConstraints ::= SEQUENCE {
//     cA                      BOOLEAN DEFAULT FALSE,
//     pathLenConstraint       INTEGER (0..MAX) OPTIONAL
// }
asn1_sequence! {
    seq BasicConstraints {
        #[default(false)] is_ca: ASN1<Boolean> = ASN1(Boolean),
        #[optional] path_len: ASN1<Integer> = ASN1(Integer),
    }
}

// certificatePolicies ::= SEQUENCE SIZE (1..MAX) OF PolicyInformation
//
// PolicyInformation ::= SEQUENCE {
//     policyIdentifier   CertPolicyId,
//     policyQualifiers   SEQUENCE SIZE (1..MAX) OF
//                             PolicyQualifierInfo OPTIONAL }
//
// CertPolicyId ::= OBJECT IDENTIFIER
//
// PolicyQualifierInfo ::= SEQUENCE {
//     policyQualifierId  PolicyQualifierId,
//     qualifier          ANY DEFINED BY policyQualifierId }
//
// PolicyQualifierId ::= OBJECT IDENTIFIER ( id-qt-cps | id-qt-unotice )
asn1_sequence! {
    seq PolicyInfo {
        policy_id: ASN1<ObjectIdentifier> = ASN1(ObjectIdentifier),
        #[optional] qualifiers: placeholder_type!() = placeholder!(SEQUENCE),
    }
}

wrap_combinator! {
    pub struct CertificatePolicies: SequenceOf<ASN1<PolicyInfo>> =>
        spec SpecCertificatePoliciesValue,
        exec<'a> CertificatePoliciesValue<'a>,
        owned CertificatePoliciesValueOwned,
    = SequenceOf(ASN1(PolicyInfo));
}

asn1_tagged!(CertificatePolicies, tag_of!(SEQUENCE));

pub type SpecCertificatePoliciesValue = Seq<SpecPolicyInfoValue>;
pub type CertificatePoliciesValue<'a> = VecDeep<PolicyInfoValue<'a>>;
pub type CertificatePoliciesValueOwned = VecDeep<PolicyInfoValueOwned>;

wrap_combinator! {
    pub struct ExtendedKeyUsage: SequenceOf<ASN1<ObjectIdentifier>> =>
        spec SpecExtendedKeyUsageValue,
        exec<'a> ExtendedKeyUsageValue<'a>,
        owned ExtendedKeyUsageValueOwned,
    = SequenceOf(ASN1(ObjectIdentifier));
}

asn1_tagged!(ExtendedKeyUsage, tag_of!(SEQUENCE));

pub type SpecExtendedKeyUsageValue = Seq<SpecObjectIdentifierValue>;
pub type ExtendedKeyUsageValue<'a> = VecDeep<ObjectIdentifierValue>;
pub type ExtendedKeyUsageValueOwned = VecDeep<ObjectIdentifierValueOwned>;

oid_match_continuation! {
    continuation ExtensionParam {
        oid(2, 5, 29, 35) =>
            AuthorityKeyIdentifier(ASN1(ExplicitTag(tag_of!(OCTET_STRING), ASN1(AuthorityKeyIdentifier)))): ASN1<ExplicitTag<ASN1<AuthorityKeyIdentifier>>>,

        oid(2, 5, 29, 14) =>
            SubjectKeyIdentifier(ASN1(ExplicitTag(tag_of!(OCTET_STRING), ASN1(OctetString)))): ASN1<ExplicitTag<ASN1<OctetString>>>,

        oid(2, 5, 29, 19) =>
            BasicConstraints(ASN1(ExplicitTag(tag_of!(OCTET_STRING), ASN1(BasicConstraints)))): ASN1<ExplicitTag<ASN1<BasicConstraints>>>,

        oid(2, 5, 29, 32) =>
            CertificatePolicies(ASN1(ExplicitTag(tag_of!(OCTET_STRING), ASN1(CertificatePolicies)))): ASN1<ExplicitTag<ASN1<CertificatePolicies>>>,

        oid(2, 5, 29, 37) =>
            ExtendedKeyUsage(ASN1(ExplicitTag(tag_of!(OCTET_STRING), ASN1(ExtendedKeyUsage)))): ASN1<ExplicitTag<ASN1<ExtendedKeyUsage>>>,

        oid(2, 5, 29, 15) =>
            KeyUsage(ASN1(ExplicitTag(tag_of!(OCTET_STRING), ASN1(BitString)))): ASN1<ExplicitTag<ASN1<BitString>>>,

        _ => Other(ASN1(OctetString)): ASN1<OctetString>,
    }
}

}
