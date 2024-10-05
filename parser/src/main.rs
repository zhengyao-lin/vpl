mod common;
pub mod asn1;
pub mod x509;

use vstd::prelude::*;

use base64::Engine;
use std::{io::{self, Read}, process::exit};

use common::*;
use x509::*;

verus! {
    fn parse_x509_bytes<'a>(bytes: &'a [u8]) -> Result<CertificateValue<'a>, ParseError> {
        let (n, cert) = Certificate.parse(bytes)?;
        if n != bytes.len() {
            return Err(ParseError::Other("trailing bytes in certificate".to_string()));
        }
        Ok(cert)
    }
}

fn parse_cert(src: &str) -> Result<(), String>
{
    let cert_base64 = src.split_whitespace().collect::<String>();
    let cert_bytes = base64::prelude::BASE64_STANDARD.decode(cert_base64)
        .map_err(|e| format!("Failed to decode Base64: {}", e))?;

    let cert = parse_x509_bytes(&cert_bytes)
        .map_err(|e| format!("Failed to parse certificate: {:?}", e))?;

    // println!("Certificate: {:?}", cert);

    Ok(())
}

pub fn main() {
    // Create a new string to store the input
    let mut input = String::new();

    // Read everything from stdin into the string
    io::stdin().read_to_string(&mut input).expect("Failed to read from stdin");

    const PREFIX: &'static str = "-----BEGIN CERTIFICATE-----";
    const SUFFIX: &'static str = "-----END CERTIFICATE-----";

    // Parse all certificates provided
    input.split(PREFIX).skip(1).for_each(|cert_enc| {
        match cert_enc.split(SUFFIX).next() {
            Some(cert_enc) => {
                match parse_cert(cert_enc) {
                    Ok(..) => {}
                    Err(e) => {
                        println!("Error: {}", e);
                        exit(1);
                    },
                }
            }
            None => {}
        }
    });
}
