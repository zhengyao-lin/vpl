use vstd::prelude::*;

use crate::asn1::*;

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

oid_match_continuation! {
    continuation ExtensionParam {
        oid(2, 5, 29, 35) =>
            AuthorityKeyIdentifier(ASN1(ExplicitTag(tag_of!(OCTET_STRING), ASN1(AuthorityKeyIdentifier)))): ASN1<ExplicitTag<ASN1<AuthorityKeyIdentifier>>>,

        oid(2, 5, 29, 14) =>
            SubjectKeyIdentifier(ASN1(ExplicitTag(tag_of!(OCTET_STRING), ASN1(OctetString)))): ASN1<ExplicitTag<ASN1<OctetString>>>,

        _ => Other(ASN1(OctetString)): ASN1<OctetString>,
    }
}

}
