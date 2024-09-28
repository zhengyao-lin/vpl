use vstd::prelude::*;

use crate::asn1::*;

use crate::common::*;
use super::macros::*;

verus! {

// RFC 2459, 4.2.1.1
asn1_sequence! {
    seq AuthorityKeyIdentifier {
        #[optional] key_id: ASN1<ImplicitTag<OctetString>> = ASN1(ImplicitTag(TagValue {
            class: TagClass::ContextSpecific,
            form: TagForm::Primitive,
            num: 0,
        }, OctetString)),

        // TODO: Parsing of GeneralNames is not implemented yet
        #[optional] auth_cert_issuer: ASN1<ImplicitTag<OctetString>> = ASN1(ImplicitTag(TagValue {
            class: TagClass::ContextSpecific,
            form: TagForm::Constructed,
            num: 1,
        }, OctetString)),

        #[optional] auth_cert_serial: ASN1<ImplicitTag<OctetString>> = ASN1(ImplicitTag(TagValue {
            class: TagClass::ContextSpecific,
            form: TagForm::Primitive,
            num: 2,
        }, OctetString)),
    }
}

oid_match_continuation! {
    continuation ExtensionParam {
        oid(2, 5, 29, 35) =>
            AuthorityKeyIdentifier(ASN1(ExplicitTag(TagValue {
                class: TagClass::Universal,
                form: TagForm::Primitive,
                num: 0x04,
            }, ASN1(AuthorityKeyIdentifier)))): ASN1<ExplicitTag<ASN1<AuthorityKeyIdentifier>>>,

        oid(2, 5, 29, 14) =>
            SubjectKeyIdentifier(ASN1(ExplicitTag(TagValue {
                class: TagClass::Universal,
                form: TagForm::Primitive,
                num: 0x04,
            }, ASN1(OctetString)))): ASN1<ExplicitTag<ASN1<OctetString>>>,

        _ => Other(ASN1(OctetString)): ASN1<OctetString>,
    }
}

}
