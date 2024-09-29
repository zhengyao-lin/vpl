use vstd::prelude::*;

use crate::asn1::*;
use crate::common::*;

use super::macros::*;

verus! {

// TODO: right now parameters are parsed as a byte sequence
oid_match_continuation! {
    continuation AlgorithmParam {
        // Signature algorithms
        // NOTE: for some of these, technically the param field should
        // be NULL (or for some should be empty), but some certificates
        // do not comply with this
        oid(1, 2, 840, 113549, 1, 1, 2) => RSASignatureWithMD2(OrdChoice(ASN1(Null), End)): OrdChoice<ASN1<Null>, End>,
        oid(1, 2, 840, 113549, 1, 1, 4) => RSASignatureWithMD5(OrdChoice(ASN1(Null), End)): OrdChoice<ASN1<Null>, End>,
        oid(1, 2, 840, 113549, 1, 1, 5) => RSASignatureWithSHA1(OrdChoice(ASN1(Null), End)): OrdChoice<ASN1<Null>, End>,
        oid(1, 2, 840, 10040, 4, 3) => DSAWithSHA1(OrdChoice(ASN1(Null), End)): OrdChoice<ASN1<Null>, End>,

        // Subject public key algorithms
        oid(1, 2, 840, 113549, 1, 1, 1) => RSAEncryption(OrdChoice(ASN1(Null), End)): OrdChoice<ASN1<Null>, End>,

        _ => Other(Tail): Tail,
    }
}

}
