mod error;
mod specs;

use vstd::prelude::*;

use std::process::ExitCode;
use base64::Engine;

use clap::{command, Parser};

use parser::common::ParseError;
use parser::common::Combinator;
use parser::asn1;
use parser::x509;

use specs::*;

use error::Error;

verus! {
    fn parse_x509_bytes<'a>(bytes: &'a [u8]) -> Result<x509::CertificateValue<'a>, ParseError> {
        let (_, cert) = asn1::ASN1(x509::Certificate).parse(bytes)?;
        Ok(cert)
    }
}

#[derive(Parser, Debug)]
#[command(long_about = None)]
struct Args {
    /// File containing the trusted root certificates
    roots: String,

    /// The certificate chain to verify
    chain: String,
}

/// Read the given PEM file and return a vector of Vec<u8>'s
/// such that each correspond to one certificate
fn read_pem_file_as_bytes(path: &str) -> Result<Vec<Vec<u8>>, Error> {
    let src = std::fs::read_to_string(path)?;
    let mut certs = vec![];

    const PREFIX: &'static str = "-----BEGIN CERTIFICATE-----";
    const SUFFIX: &'static str = "-----END CERTIFICATE-----";

    for chunk in src.split(PREFIX).skip(1) {
        let Some(cert_src) = chunk.split(SUFFIX).next() else {
            return Err(Error::Other("BEGIN CERTIFICATE without matching END CERTIFICATE".to_string()));
        };

        let cert_base64 = cert_src.split_whitespace().collect::<String>();
        let cert_bytes = base64::prelude::BASE64_STANDARD.decode(cert_base64)
            .map_err(|e| Error::Other(format!("Failed to decode Base64: {}", e)))?;

        certs.push(cert_bytes);
    }

    Ok(certs)
}

fn main_args(args: Args) -> Result<(), Error> {
    // Parse roots and chain PEM files
    let roots_bytes = read_pem_file_as_bytes(&args.roots)?;
    let chain_bytes = read_pem_file_as_bytes(&args.chain)?;

    let roots = roots_bytes.iter().map(|cert_bytes| {
        parse_x509_bytes(cert_bytes)
    }).collect::<Result<Vec<_>, _>>()?;

    let chain = chain_bytes.iter().map(|cert_bytes| {
        parse_x509_bytes(cert_bytes)
    }).collect::<Result<Vec<_>, _>>()?;

    println!("{} root certificate(s)", roots.len());
    println!("{} certificate(s) in the chain", chain.len());

    for (i, cert) in chain.iter().enumerate() {
        println!("cert {}:", i);
        println!("  issuer: {}", cert.tbs_certificate.issuer);
        println!("  subject: {}", cert.tbs_certificate.subject);
    }

    // Check that for each i, cert[i + 1] issued cert[i]
    for i in 0..chain.len() - 1 {
        // Issuer of cert[i] is the same as the subject of cert[i + 1]
        let issuer = &chain[i + 1].tbs_certificate.subject;
        let subject = &chain[i].tbs_certificate.issuer;

        if same_name(issuer, subject) {
            println!("cert {} issued by cert {}", i + 1, i);
        } else {
            println!("cert {} not issued by cert {}", i + 1, i);
        }
    }

    // Find root certificates that issued the last certificate in the chain
    let issuer = &chain[chain.len() - 1].tbs_certificate.issuer;
    for (i, root) in roots.iter().enumerate() {
        if same_name(issuer, &root.tbs_certificate.subject) {
            println!("last cert issued by root cert {}: {}", i, root.tbs_certificate.subject);
        }
    }

    Ok(())
}

// https://github.com/openssl/openssl/blob/ed6862328745c51c2afa2b6485cc3e275d543c4e/crypto/x509/v3_purp.c#L953

pub fn main() -> ExitCode {
    match main_args(Args::parse()) {
        Ok(..) => ExitCode::from(0),
        Err(err) => {
            eprintln!("{}", err);
            ExitCode::from(1)
        }
    }
}
