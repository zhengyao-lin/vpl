use vstd::prelude::*;

use crate::asn1::*;

use crate::common::*;
use super::macros::*;

verus! {

match_continuation! {
    continuation ExtensionParam<'a>(ObjectIdentifierValue, spec SpecObjectIdentifierValue) {
        oid!(2, 5, 29, 35), spec seq![ 2 as UInt, 5, 29, 35 ] => AuthorityKeyIdentifier, ASN1<OctetString>, ASN1(OctetString),
        _ => Other, ASN1<OctetString>, ASN1(OctetString),
    }
}

}
