use vstd::prelude::*;

use crate::asn1::*;
use crate::common::*;
use super::*;

verus! {

// Certificate  ::=  SEQUENCE  {
//     tbsCertificate       TBSCertificate,
//     signatureAlgorithm   AlgorithmIdentifier,
//     signatureValue       BIT STRING
// }
asn1_sequence! {
    seq CertificateInner {
        cert: Cached<ASN1<TBSCertificate>> = Cached(ASN1(TBSCertificate)),
        sig_alg: ASN1<AlgorithmIdentifier> = ASN1(AlgorithmIdentifier),
        sig: ASN1<BitString> = ASN1(BitString),
    }
}

wrap_combinator! {
    pub struct Certificate: Cached<ASN1<CertificateInner>> = Cached(ASN1(CertificateInner));
}

pub type SpecCertificateValue = SpecCertificateInnerValue;
pub type CertificateValue<'a> = CachedValue<'a, CertificateInnerValue<'a>>;

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
