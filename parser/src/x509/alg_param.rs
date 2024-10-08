use vstd::prelude::*;

use crate::asn1::*;
use crate::common::*;

use super::macros::*;

verus! {

asn1! {
    // Dss-Parms  ::=  SEQUENCE  {
    //     p             INTEGER,
    //     q             INTEGER,
    //     g             INTEGER
    // }
    seq DSAParam {
        p: ASN1<BigInt> = ASN1(BigInt),
        q: ASN1<BigInt> = ASN1(BigInt),
        g: ASN1<BigInt> = ASN1(BigInt),
    }

    // NOTE: This is the format of the public key field of subject public key info
    // not the format of AlgorithmIdentifier.param
    //
    // RSAPublicKey ::= SEQUENCE {
    //     modulus            INTEGER, -- n
    //     publicExponent     INTEGER  -- e --
    // }
    seq RSAParam {
        modulus: ASN1<BigInt> = ASN1(BigInt),
        exponent: ASN1<BigInt> = ASN1(BigInt),
    }
}

// TODO: DSA, ECDSA, etc.
oid_match_continuation! {
    continuation AlgorithmParam {
        // Signature algorithms
        // NOTE: for some of these, technically the param field should
        // be NULL (or for some should be empty), but some certificates
        // do not comply with this
        oid(1, 2, 840, 113549, 1, 1, 2) => RSASignatureWithMD2(OrdChoice(ASN1(Null), End)): OrdChoice<ASN1<Null>, End>,
        oid(1, 2, 840, 113549, 1, 1, 4) => RSASignatureWithMD5(OrdChoice(ASN1(Null), End)): OrdChoice<ASN1<Null>, End>,
        oid(1, 2, 840, 113549, 1, 1, 5) => RSASignatureWithSHA1(OrdChoice(ASN1(Null), End)): OrdChoice<ASN1<Null>, End>,

        oid(1, 2, 840, 113549, 1, 1, 11) => RSASignatureWithSHA256(OrdChoice(ASN1(Null), End)): OrdChoice<ASN1<Null>, End>,
        oid(1, 2, 840, 113549, 1, 1, 12) => RSASignatureWithSHA384(OrdChoice(ASN1(Null), End)): OrdChoice<ASN1<Null>, End>,
        oid(1, 2, 840, 113549, 1, 1, 13) => RSASignatureWithSHA512(OrdChoice(ASN1(Null), End)): OrdChoice<ASN1<Null>, End>,
        oid(1, 2, 840, 113549, 1, 1, 14) => RSASignatureWithSHA224(OrdChoice(ASN1(Null), End)): OrdChoice<ASN1<Null>, End>,

        oid(1, 2, 840, 10040, 4, 1) => DSASignature(OrdChoice(ASN1(DSAParam), End)): OrdChoice<ASN1<DSAParam>, End>,

        // Subject public key algorithms
        oid(1, 2, 840, 113549, 1, 1, 1) => RSAEncryption(OrdChoice(ASN1(Null), End)): OrdChoice<ASN1<Null>, End>,

        _ => Other(Tail): Tail,
    }
}

impl<'a> PolyfillEq for DSAParamValue<'a> {
    fn polyfill_eq(&self, other: &Self) -> bool {
        self.p.polyfill_eq(&other.p) && self.q.polyfill_eq(&other.q) && self.g.polyfill_eq(&other.g)
    }
}

impl<'a> PolyfillEq for AlgorithmParamValue<'a> {
    fn polyfill_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (AlgorithmParamValue::RSASignatureWithMD2(a), AlgorithmParamValue::RSASignatureWithMD2(b)) => a.polyfill_eq(b),
            (AlgorithmParamValue::RSASignatureWithMD5(a), AlgorithmParamValue::RSASignatureWithMD5(b)) => a.polyfill_eq(b),
            (AlgorithmParamValue::RSASignatureWithSHA1(a), AlgorithmParamValue::RSASignatureWithSHA1(b)) => a.polyfill_eq(b),
            (AlgorithmParamValue::RSASignatureWithSHA256(a), AlgorithmParamValue::RSASignatureWithSHA256(b)) => a.polyfill_eq(b),
            (AlgorithmParamValue::RSASignatureWithSHA384(a), AlgorithmParamValue::RSASignatureWithSHA384(b)) => a.polyfill_eq(b),
            (AlgorithmParamValue::RSASignatureWithSHA512(a), AlgorithmParamValue::RSASignatureWithSHA512(b)) => a.polyfill_eq(b),
            (AlgorithmParamValue::RSASignatureWithSHA224(a), AlgorithmParamValue::RSASignatureWithSHA224(b)) => a.polyfill_eq(b),
            (AlgorithmParamValue::DSASignature(a), AlgorithmParamValue::DSASignature(b)) => a.polyfill_eq(b),
            (AlgorithmParamValue::RSAEncryption(a), AlgorithmParamValue::RSAEncryption(b)) => a.polyfill_eq(b),
            (AlgorithmParamValue::Other(a), AlgorithmParamValue::Other(b)) => a.polyfill_eq(b),
            (AlgorithmParamValue::Unreachable, AlgorithmParamValue::Unreachable) => true,
            _ => false,
        }
    }
}

}
