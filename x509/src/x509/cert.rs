use vstd::prelude::*;

use crate::asn1::*;
use crate::common::*;
use super::*;

verus! {

/// Certificate  ::=  SEQUENCE  {
///     tbsCertificate       TBSCertificate,
///     signatureAlgorithm   AlgorithmIdentifier,
///     signatureValue       BIT STRING
/// }
pub type CertificateInner = Mapped<
    LengthWrapped<
        Pair<ASN1<TBSCertificate>,
        Pair<ASN1<AlgorithmIdentifier>,
        ASN1<BitString>,
    >>>,
    CertificateMapper>;

wrap_combinator! {
    struct Certificate: CertificateInner =>
        spec SpecCertificateValue,
        exec<'a> CertificateValue<'a>,
        owned CertificateValueOwned,
    =
        Mapped {
            inner: LengthWrapped(
                Pair(ASN1(TBSCertificate),
                Pair(ASN1(AlgorithmIdentifier),
                ASN1(BitString)),
            )),
            mapper: CertificateMapper,
        };
}

asn1_tagged!(Certificate, TagValue {
    class: TagClass::Universal,
    form: TagForm::Constructed,
    num: 0x10,
});

#[derive(Debug, View, PolyfillClone)]
pub struct CertificatePoly<Cert, Alg, Signature> {
    pub cert: Cert,
    pub alg: Alg,
    pub signature: Signature,
}

pub type SpecCertificateValue = CertificatePoly<SpecTBSCertificateValue, SpecAlgorithmIdentifierValue, SpecBitStringValue>;
pub type CertificateValue<'a> = CertificatePoly<TBSCertificateValue<'a>, AlgorithmIdentifierValue<'a>, BitStringValue<'a>>;
pub type CertificateValueOwned = CertificatePoly<TBSCertificateValueOwned, AlgorithmIdentifierValueOwned, BitStringValueOwned>;

type CertificateFrom<Cert, Alg, Signature> = PairValue<Cert, PairValue<Alg, Signature>>;

impl<Cert, Alg, Signature> SpecFrom<CertificatePoly<Cert, Alg, Signature>> for CertificateFrom<Cert, Alg, Signature> {
    closed spec fn spec_from(s: CertificatePoly<Cert, Alg, Signature>) -> Self {
        PairValue(s.cert, PairValue(s.alg, s.signature))
    }
}

impl<Cert, Alg, Signature> SpecFrom<CertificateFrom<Cert, Alg, Signature>> for CertificatePoly<Cert, Alg, Signature> {
    closed spec fn spec_from(s: CertificateFrom<Cert, Alg, Signature>) -> Self {
        CertificatePoly {
            cert: s.0,
            alg: s.1.0,
            signature: s.1.1,
        }
    }
}

impl<Cert: View, Alg: View, Signature: View> From<CertificatePoly<Cert, Alg, Signature>> for CertificateFrom<Cert, Alg, Signature> {
    fn ex_from(s: CertificatePoly<Cert, Alg, Signature>) -> Self {
        PairValue(s.cert, PairValue(s.alg, s.signature))
    }
}

impl<Cert: View, Alg: View, Signature: View> From<CertificateFrom<Cert, Alg, Signature>> for CertificatePoly<Cert, Alg, Signature> {
    fn ex_from(s: CertificateFrom<Cert, Alg, Signature>) -> Self {
        CertificatePoly {
            cert: s.0,
            alg: s.1.0,
            signature: s.1.1,
        }
    }
}

#[derive(Debug, View)]
pub struct CertificateMapper;

impl SpecIso for CertificateMapper {
    type Src = CertificateFrom<SpecTBSCertificateValue, SpecAlgorithmIdentifierValue, SpecBitStringValue>;
    type Dst = SpecCertificateValue;

    proof fn spec_iso(s: Self::Src) {}
    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl Iso for CertificateMapper {
    type Src<'a> = CertificateFrom<TBSCertificateValue<'a>, AlgorithmIdentifierValue<'a>, BitStringValue<'a>>;
    type Dst<'a> = CertificateValue<'a>;

    type SrcOwned = CertificateFrom<TBSCertificateValueOwned, AlgorithmIdentifierValueOwned, BitStringValueOwned>;
    type DstOwned = CertificateValueOwned;
}

}
