use vstd::prelude::*;

use crate::asn1::*;

use crate::common::*;
use super::macros::*;

verus! {

oid_match_continuation! {
    continuation ExtensionParam {
        oid(2, 5, 29, 35) => AuthorityKeyIdentifier(ASN1(OctetString)): ASN1<OctetString>,
        _ => Other(ASN1(OctetString)): ASN1<OctetString>,
    }
}

}
