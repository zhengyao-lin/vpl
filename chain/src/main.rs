use std::{io::{self, Read}, process::exit};

use base64::Engine;

use parser::asn1::*;
use parser::common::*;
use parser::x509;

/// TODO: due to a Verus export bug, we can't use this in verus! block yet
fn parse_x509_bytes(bytes: &[u8]) -> Result<x509::CertificateValue, ParseError> {
    let (_, cert) = ASN1(x509::Certificate).parse(bytes)?;
    Ok(cert)
}

fn hexdump(data: &[u8]) {
    for chunk in data.chunks(16) {
        for byte in chunk {
            print!("{:02x} ", byte);
        }
        println!();
    }
}

fn parse_cert(src: &str) -> Result<(), String>
{
    let cert_base64 = src.split_whitespace().collect::<String>();
    let cert_bytes = base64::prelude::BASE64_STANDARD.decode(cert_base64)
        .map_err(|e| format!("Failed to decode Base64: {}", e))?;

    let cert = parse_x509_bytes(&cert_bytes)
        .map_err(|e| format!("Failed to parse certificate: {:?}", e))?;

    println!("Certificate: {:?}", cert);

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
