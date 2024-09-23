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
    pub struct Certificate: CertificateInner =>
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

mapper! {
    pub struct CertificateMapper;

    for <Cert, Alg, Signature>
    from CertificateFrom where type CertificateFrom<Cert, Alg, Signature> = PairValue<Cert, PairValue<Alg, Signature>>;
    to CertificatePoly where pub struct CertificatePoly<Cert, Alg, Signature> {
        pub cert: Cert,
        pub alg: Alg,
        pub signature: Signature,
    }

    spec SpecCertificateValue with <SpecTBSCertificateValue, SpecAlgorithmIdentifierValue, SpecBitStringValue>;
    exec CertificateValue<'a> with <TBSCertificateValue<'a>, AlgorithmIdentifierValue<'a>, BitStringValue<'a>>;
    owned CertificateValueOwned with <TBSCertificateValueOwned, AlgorithmIdentifierValueOwned, BitStringValueOwned>;

    forward(x) {
        CertificatePoly {
            cert: x.0,
            alg: x.1.0,
            signature: x.1.1,
        }
    }

    backward(y) {
        PairValue(y.cert, PairValue(y.alg, y.signature))
    }
}

}

#[cfg(test)]
mod test {
    use super::*;
    use base64::Engine;

    verus! {
        /// Check that all trait bounds and preconditions are satisfied
        #[test]
        fn is_combinator() {
            let _ = ASN1(Certificate).parse(&[]);
        }
    }

    fn parse_cert(src: &str) -> Result<(), String>
    {
        let cert_base64 = src.split_whitespace().collect::<String>();
        let cert_bytes = base64::prelude::BASE64_STANDARD.decode(cert_base64)
            .map_err(|e| format!("Failed to decode Base64: {}", e))?;

        let cert = ASN1(Certificate).parse(&cert_bytes)
            .map_err(|e| format!("Failed to parse certificate"))?;

        println!("Certificate: {:?}", cert);

        Ok(())
    }

    /// Test the final combinator on some root certificates
    #[test]
    fn roots_pem() {
        let roots = include_str!("../../tests/data/roots.pem");
        const PREFIX: &'static str = "-----BEGIN CERTIFICATE-----";
        const SUFFIX: &'static str = "-----END CERTIFICATE-----";

        // Parse all certificates provided
        roots.split(PREFIX).skip(1).for_each(|cert_enc| {
            match cert_enc.split(SUFFIX).next() {
                Some(cert_enc) => {
                    assert!(parse_cert(cert_enc).is_ok());
                }
                None => {}
            }
        });
    }
}
