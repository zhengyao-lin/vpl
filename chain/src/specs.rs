// Specifications for some base operations on X.509 certificates
// e.g. comparing distinguished names, checking issuers

use vstd::prelude::*;

use chrono::prelude::NaiveDate;

use polyfill::*;

use parser::{*, asn1::*, x509::*};
use parser::OptionDeep::*;

use vpl::*;

use crate::hash;

verus! {

/// The top-level spec stating when a certificate chain
/// is considered valid with respect to given policy,
/// root certificates, and final domain
pub open spec fn spec_valid_domain(
    policy: SpecProgram,
    roots: Seq<SpecCertificateValue>,
    chain: Seq<SpecCertificateValue>,
    domain: SpecStringLiteral,
) -> bool
{
    let leaf = chain[0];
    let merged_policy = SpecProgram {
        rules: policy.rules + spec_gen_all_facts(roots, chain, domain),
    };

    &&& chain.len() > 0

    // Exists a proof of the final goal certVerifiedChain(cert(0))
    &&& exists |thm: SpecTheorem| {
        &&& #[trigger] thm.wf(merged_policy)
        &&& thm.stmt == spec_app!("certVerifiedChain", spec_cert_name(0))
    }
}

/// Generate all facts about the root certificates
/// cert chain, and the domain
pub open spec fn spec_gen_all_facts(
    roots: Seq<SpecCertificateValue>,
    chain: Seq<SpecCertificateValue>,
    domain: SpecStringLiteral,
) -> Seq<SpecRule>
{
    // issuer() facts between chain certs
    spec_gen_chain_issuer_facts(chain) +

    // Facts about each individual chain cert
    spec_gen_chain_facts(chain) +

    // Root cert issuer() and other facts
    spec_gen_root_facts(roots, chain) +

    // Finally, the domain to be validated
    seq![ spec_domain_fact(domain) ]
}

/// Generate facts about root certs and prune
/// unused root certs
pub open spec fn spec_gen_root_facts(
    roots: Seq<SpecCertificateValue>,
    chain: Seq<SpecCertificateValue>,
) -> Seq<SpecRule>
{
    Seq::new(roots.len(),
        |i| {
            let issue_facts = Seq::new(chain.len(), |j|
                if spec_likely_issued(roots[i], chain[j]) &&
                    spec_verify_signature(roots[i], chain[j]) {
                    seq![ spec_issuer_fact(i + chain.len(), j) ]
                } else {
                    seq![]
                }
            ).flatten();

            // Pruning happens here: if a root certificate did not
            // issue any of the chain certs, we omit it
            if issue_facts.len() != 0 {
                issue_facts + spec_gen_cert_facts(roots[i], i + chain.len())
            } else {
                issue_facts
            }
        }
    ).flatten()
}

/// Generate facts about chain certs issuing each other
pub open spec fn spec_gen_chain_issuer_facts(
    chain: Seq<SpecCertificateValue>,
) -> Seq<SpecRule>
{
    Seq::new((chain.len() - 1) as nat,
        |i: int| if spec_likely_issued(chain[i + 1], chain[i]) &&
            spec_verify_signature(chain[i + 1], chain[i]) {
            seq![ spec_issuer_fact(i + 1, i) ]
        } else {
            seq![]
        }
    ).flatten()
}

pub open spec fn spec_gen_chain_facts(
    chain: Seq<SpecCertificateValue>,
) -> Seq<SpecRule>
{
    Seq::new(chain.len(), |i| spec_gen_cert_facts(chain[i], i)).flatten()
}

/// Construct an issuer fact of the form issuer(cert_i, cert_j)
/// NOTE: i is the issuer of j
pub open spec fn spec_issuer_fact(i: int, j: int) -> SpecRule
{
    spec_fact!("issuer", spec_cert_name(j), spec_cert_name(i))
}

/// Construct envDomain(domain)
pub open spec fn spec_domain_fact(domain: SpecStringLiteral) -> SpecRule
{
    spec_fact!("envDomain", spec_str!(domain))
}

/// Construct term cert(i)
pub open spec fn spec_cert_name(i: int) -> SpecTerm
{
    // NOTE: instead of doing cert_i as in the original Hammurabi
    // we use cert(i) to avoid int::to_string in the spec
    spec_app!("cert", spec_int!(i))
}

/// If the the issuer likely issued the subject.
/// Similar to https://github.com/openssl/openssl/blob/ed6862328745c51c2afa2b6485cc3e275d543c4e/crypto/x509/v3_purp.c#L963
pub open spec fn spec_likely_issued(issuer: SpecCertificateValue, subject: SpecCertificateValue) -> bool
{
    &&& spec_same_name(issuer.cert.subject, subject.cert.issuer)
    &&& spec_check_auth_key_id(issuer, subject)
    // TODO: more conditions
}

/// Compare two Names
/// References:
/// - RFC 2459, 4.1.2.4
/// - https://github.com/openssl/openssl/blob/ed6862328745c51c2afa2b6485cc3e275d543c4e/crypto/x509/x509_cmp.c#L254
///
/// Basically equality, except that two PrintableString's
/// are considered equal modulo upper/lower cases, leading/trailing white spaces
/// and multiple white spaces in the middle are considered as one white space.
pub open spec fn spec_same_name(a: SpecNameValue, b: SpecNameValue) -> bool {
    &&& a.len() == b.len()
    &&& forall |i| #![auto] 0 <= i < a.len() ==> spec_same_rdn(a[i], b[i])
}

/// Continuing the spec of same_name
pub open spec fn spec_same_rdn(a: SpecRDNValue, b: SpecRDNValue) -> bool {
    &&& a.len() == b.len()
    &&& forall |i| #![auto] 0 <= i < a.len() ==> spec_same_attr(a[i], b[i])
}

/// Continuing the spec of same_name
pub open spec fn spec_same_attr(a: SpecAttributeTypeAndValueValue, b: SpecAttributeTypeAndValueValue) -> bool {
    &&& a.typ =~= b.typ
    &&& match (a.value, b.value) {
        // TODO: normalize PrintableStrings
        (SpecDirectoryStringValue::PrintableString(a), SpecDirectoryStringValue::PrintableString(b)) => a =~= b,
        _ => a.value =~= b.value
    }
}

/// Given potential issuer and subject,
/// if the subject has a AuthorityKeyIdentifier extension,
/// and the issuer has a SubjectKeyIdentifier extension,
/// we compare that:
/// 1. subject.akid.key_id matches issuer.skid
/// 2. (if exists) subject.akit.serial matches issuer.serial
/// 3. TODO: subject.akid.auth_cert_issuer matches
///
/// References:
/// - RFC 2459, 4.2.1.1
/// - https://github.com/openssl/openssl/blob/ed6862328745c51c2afa2b6485cc3e275d543c4e/crypto/x509/v3_purp.c#L1002
pub open spec fn spec_check_auth_key_id(issuer: SpecCertificateValue, subject: SpecCertificateValue) -> bool {
    if let Some(akid) = spec_get_auth_key_id(subject) {
        &&& akid.key_id matches OptionDeep::Some(id)
            ==> spec_get_subject_key_id(issuer) matches Some(skid)
            ==> id =~= skid
        &&& akid.auth_cert_serial matches OptionDeep::Some(serial) ==> serial =~= issuer.cert.serial
        // TODO auth_cert_issuer
    } else {
        true
    }
}

/// Get the first extension with the given OID
/// return (critical, param)
pub open spec fn spec_get_extension(cert: SpecCertificateValue, oid: SpecObjectIdentifierValue) -> OptionDeep<SpecExtensionValue>
{
    if let Some(exts) = cert.cert.extensions {
        spec_get_extension_helper(exts, oid)
    } else {
        None
    }
}

pub open spec fn spec_get_extension_helper(exts: Seq<SpecExtensionValue>, oid: SpecObjectIdentifierValue) -> OptionDeep<SpecExtensionValue>
    decreases exts.len()
{
    if exts.len() == 0 {
        None
    } else {
        if exts[0].id =~= oid {
            Some(exts[0])
        } else {
            spec_get_extension_helper(exts.drop_first(), oid)
        }
    }
}

/// Get the AuthorityKeyIdentifier extension if it exists
pub open spec fn spec_get_auth_key_id(cert: SpecCertificateValue) -> OptionDeep<SpecAuthorityKeyIdentifierValue>
{
    if let Some(ext) = spec_get_extension(cert, spec_oid!(2, 5, 29, 35)) {
        if let SpecExtensionParamValue::AuthorityKeyIdentifier(param) = ext.param {
            Some(param)
        } else {
            None
        }
    } else {
        None
    }
}

/// Get the SubjectKeyIdentifier extension if it exists
pub open spec fn spec_get_subject_key_id(cert: SpecCertificateValue) -> OptionDeep<Seq<u8>>
{
    if let Some(ext) = spec_get_extension(cert, spec_oid!(2, 5, 29, 14)) {
        if let SpecExtensionParamValue::SubjectKeyIdentifier(param) = ext.param {
            Some(param)
        } else {
            None
        }
    } else {
        None
    }
}

/// Verify the subject cert's signature using issuer's public key
pub open spec fn spec_verify_signature(issuer: SpecCertificateValue, subject: SpecCertificateValue) -> bool
{
    // Signature algorithm is consistent in the subject cert
    &&& subject.sig_alg =~= subject.cert.signature

    // TODO: actually check the signature
}

/// TODO: missing support for TeletexString, UniversalString, BMPString
pub open spec fn spec_dir_string_to_string(dir: SpecDirectoryStringValue) -> OptionDeep<Seq<char>>
{
    match dir {
        SpecDirectoryStringValue::PrintableString(s) => Some(s),
        SpecDirectoryStringValue::UTF8String(s) => Some(s),
        SpecDirectoryStringValue::IA5String(s) => Some(s),
        SpecDirectoryStringValue::TeletexString(s) => None,
        SpecDirectoryStringValue::UniversalString(s) => None,
        SpecDirectoryStringValue::BMPString(s) => None,
    }
}

pub open spec fn spec_get_rdn(name: SpecNameValue, oid: SpecObjectIdentifierValue) -> OptionDeep<Seq<char>>
    decreases name.len()
{
    if name.len() == 0 {
        None
    } else {
        if name[0].len() == 1 && name[0][0].typ == oid {
            spec_dir_string_to_string(name[0][0].value)
        } else {
            spec_get_rdn(name.drop_first(), oid)
        }
    }
}

pub open spec fn spec_oid_to_str(oid: SpecObjectIdentifierValue) -> Seq<char>
{
    seq_join(Seq::new(oid.len(), |i| spec_u64_to_string(oid[i])), "."@)
}

/// Specify the facts to be generated from a certificate
pub open spec fn spec_gen_cert_facts(cert: SpecCertificateValue, i: int) -> Seq<SpecRule>
{
    // Using ASN1(CertificateInner)@ instead of CertificateValue@
    // here since due to CachedValue::serialized()
    let ser_cert = ASN1(CertificateInner)@.spec_serialize(cert).unwrap();

    seq![
        spec_fact!("fingerprint",
            spec_cert_name(i),
            spec_str!(hash::spec_to_hex_upper(hash::spec_sha256_digest(ser_cert))),
        ),

        spec_fact!("version", spec_cert_name(i), spec_int!(cert.cert.version as int)),

        spec_fact!("signatureAlgorithm", spec_cert_name(i), spec_str!(spec_oid_to_str(cert.sig_alg.id))),

        spec_fact!("notAfter", spec_cert_name(i), spec_int!(spec_x509_time_to_timestamp(cert.cert.validity.not_after).unwrap() as int)),
        spec_fact!("notBefore", spec_cert_name(i), spec_int!(spec_x509_time_to_timestamp(cert.cert.validity.not_before).unwrap() as int)),

        spec_gen_spki_dsa_param_fact(cert, i),
        spec_gen_spki_rsa_param_fact(cert, i),
    ] + spec_gen_subject_name_info(cert, i) + spec_gen_extension_facts(cert, i)
}

/// Extract info about the subject name
pub open spec fn spec_gen_subject_name_info(cert: SpecCertificateValue, i: int) -> Seq<SpecRule>
{
    seq![
        spec_fact!("subject", spec_cert_name(i),
            // common name
            spec_str!(spec_get_rdn(cert.cert.subject, spec_oid!(2, 5, 4, 3)).unwrap_or("".view())),
            // country
            spec_str!(spec_get_rdn(cert.cert.subject, spec_oid!(2, 5, 4, 6)).unwrap_or("".view())),
            // locality
            spec_str!(spec_get_rdn(cert.cert.subject, spec_oid!(2, 5, 4, 7)).unwrap_or("".view())),
            // state or province name
            spec_str!(spec_get_rdn(cert.cert.subject, spec_oid!(2, 5, 4, 8)).unwrap_or("".view())),
            // organization name
            spec_str!(spec_get_rdn(cert.cert.subject, spec_oid!(2, 5, 4, 10)).unwrap_or("".view())),
        ),

        // TODO: duplicate with the subject pred?
        spec_fact!("commonName", spec_cert_name(i),
            spec_str!(spec_get_rdn(cert.cert.subject, spec_oid!(2, 5, 4, 3)).unwrap_or("".view())),
        ),

        spec_fact!("country", spec_cert_name(i),
            spec_str!(spec_get_rdn(cert.cert.subject, spec_oid!(2, 5, 4, 6)).unwrap_or("".view())),
        ),

        spec_fact!("givenName", spec_cert_name(i),
            spec_str!(spec_get_rdn(cert.cert.subject, spec_oid!(2, 5, 4, 42)).unwrap_or("".view())),
        ),

        spec_fact!("localityName", spec_cert_name(i),
            spec_str!(spec_get_rdn(cert.cert.subject, spec_oid!(2, 5, 4, 7)).unwrap_or("".view())),
        ),

        spec_fact!("organizationName", spec_cert_name(i),
            spec_str!(spec_get_rdn(cert.cert.subject, spec_oid!(2, 5, 4, 10)).unwrap_or("".view())),
        ),

        spec_fact!("postalCode", spec_cert_name(i),
            spec_str!(spec_get_rdn(cert.cert.subject, spec_oid!(2, 5, 4, 17)).unwrap_or("".view())),
        ),

        spec_fact!("stateOrProvinceName", spec_cert_name(i),
            spec_str!(spec_get_rdn(cert.cert.subject, spec_oid!(2, 5, 4, 8)).unwrap_or("".view())),
        ),

        spec_fact!("streetAddress", spec_cert_name(i),
            spec_str!(spec_get_rdn(cert.cert.subject, spec_oid!(2, 5, 4, 9)).unwrap_or("".view())),
        ),

        spec_fact!("surname", spec_cert_name(i),
            spec_str!(spec_get_rdn(cert.cert.subject, spec_oid!(2, 5, 4, 4)).unwrap_or("".view())),
        ),
    ]
}

pub open spec fn spec_gen_spki_dsa_param_fact(cert: SpecCertificateValue, i: int) -> SpecRule
{
    match cert.cert.subject_key.alg.param {
        SpecAlgorithmParamValue::DSASignature(Either::Left(param)) => {
            spec_fact!("spkiDSAParameters",
                spec_cert_name(i),
                spec_int!((param.p.len() - 1) as usize * 8),
                spec_int!((param.q.len() - 1) as usize * 8),
                spec_int!((param.g.len() - 1) as usize * 8),
            )
        }

        _ => spec_fact!("spkiDSAParameters", spec_cert_name(i), spec_atom!("na".view()), spec_atom!("na".view()), spec_atom!("na".view())),
    }
}

pub open spec fn spec_gen_spki_rsa_param_fact(cert: SpecCertificateValue, i: int) -> SpecRule
{
    match cert.cert.subject_key.alg.param {
        SpecAlgorithmParamValue::RSAEncryption(..) => {
            // Parse the public key field to get the modulus length

            // First byte of cert.cert.subject_key.pub_key.0 indicates the number of trailing zeros
            // in ASN.1 bit string
            let pub_key = BitStringValue::spec_bytes(cert.cert.subject_key.pub_key);

            // TODO: we need to enforce at the parser that this must succeed
            let (_, parsed) = ASN1(RSAParam)@.spec_parse(pub_key).unwrap();

            spec_fact!("spkiRSAModLength", spec_cert_name(i), spec_int!((parsed.modulus.len() - 1) as usize * 8))
        }

        _ => spec_fact!("spkiRSAModLength", spec_cert_name(i), spec_atom!("na".view())),
    }
}

/// Generate facts about X.509 extensions
pub open spec fn spec_gen_extension_facts(cert: SpecCertificateValue, i: int) -> Seq<SpecRule>
{
    spec_gen_ext_basic_constraints_facts(cert, i) +
    spec_gen_ext_key_usage_facts(cert, i)
}

pub open spec fn spec_gen_ext_basic_constraints_facts(cert: SpecCertificateValue, i: int) -> Seq<SpecRule>
{
    if let Some(ext) = spec_get_extension(cert, spec_oid!(2, 5, 29, 19)) {
        if let SpecExtensionParamValue::BasicConstraints(param) = ext.param {
            seq![
                spec_fact!("basicConstraintsExt", spec_cert_name(i), spec_atom!("true".view())),
                spec_fact!("basicConstraintsCritical", spec_cert_name(i), spec_atom!((if ext.critical { "true" } else { "false" }).view())),
                spec_fact!("isCA", spec_cert_name(i), spec_atom!((if param.is_ca { "true" } else { "false" }).view())),

                if let Some(path_len) = param.path_len {
                    spec_fact!("pathLimit", spec_cert_name(i), spec_int!(path_len as int))
                } else {
                    spec_fact!("pathLimit", spec_cert_name(i), spec_atom!("none".view()))
                },
            ]
        } else {
            seq![
                spec_fact!("basicConstraintsExt", spec_cert_name(i), spec_atom!("false".view())),
            ]
        }
    } else {
        seq![
            spec_fact!("basicConstraintsExt", spec_cert_name(i), spec_atom!("false".view())),
        ]
    }
}

pub open spec fn spec_gen_ext_key_usage_facts_helper(usages: Seq<Seq<char>>, param: SpecBitStringValue, i: int, j: int) -> Seq<SpecRule>
    decreases j
{
    if j <= 0 {
        seq![]
    } else if BitStringValue::spec_has_bit(param, j - 1) {
        spec_gen_ext_key_usage_facts_helper(usages, param, i, j - 1) +
        seq![ spec_fact!("keyUsage", spec_cert_name(i), spec_atom!(usages[j - 1])) ]
    } else {
        spec_gen_ext_key_usage_facts_helper(usages, param, i, j - 1)
    }
}

pub open spec fn spec_gen_ext_key_usage_facts(cert: SpecCertificateValue, i: int) -> Seq<SpecRule>
{
    if let Some(ext) = spec_get_extension(cert, spec_oid!(2, 5, 29, 15)) {
        if let SpecExtensionParamValue::KeyUsage(param) = ext.param {
            let usages = seq![
                "digitalSignature".view(),
                "nonRepudiation".view(),
                "keyEncipherment".view(),
                "dataEncipherment".view(),
                "keyAgreement".view(),
                "keyCertSign".view(),
                "cRLSign".view(),
                "encipherOnly".view(),
                "decipherOnly".view(),
            ];

            seq![
                spec_fact!("keyUsageExt", spec_cert_name(i), spec_atom!("true".view())),
                spec_fact!("keyUsageCritical", spec_cert_name(i), spec_atom!((if ext.critical { "true" } else { "false" }).view())),
            ] +
            spec_gen_ext_key_usage_facts_helper(usages, param, i, usages.len() as int)
        } else {
            seq![
                spec_fact!("keyUsageExt", spec_cert_name(i), spec_atom!("false".view())),
            ]
        }
    } else {
        seq![
            spec_fact!("keyUsageExt", spec_cert_name(i), spec_atom!("false".view())),
        ]
    }
}

pub closed spec fn spec_x509_time_to_timestamp(time: SpecTimeValue) -> Option<i64>;

/// Convert an X.509 Time to a UNIX timestamp
/// NOTE: this implementation is unverified and trusted
#[verifier::external_body]
pub fn x509_time_to_timestamp(time: &TimeValue) -> (res: Option<i64>)
    ensures res == spec_x509_time_to_timestamp(time@)
{
    // Convert UTCTime/GeneralizedTime to chrono::NaiveDateTime
    let dt = match time {
        TimeValue::UTCTime(t) => {
            let date = NaiveDate::from_ymd_opt(t.year as i32, t.month as u32, t.day as u32)?;
            let naive = date.and_hms_opt(
                t.hour as u32,
                t.minute as u32,
                *t.second.as_ref().unwrap_or(&0) as u32,
            )?;

            if let UTCTimeZone::UTC = t.time_zone {
                naive.and_utc()
            } else {
                return Option::None;
            }
        }
        TimeValue::GeneralizedTime(t) => {
            let date = NaiveDate::from_ymd_opt(t.year as i32, t.month as u32, t.day as u32)?;
            let naive = date.and_hms_opt(
                t.hour as u32,
                *t.minute.as_ref().unwrap_or(&0) as u32,
                *t.second.as_ref().unwrap_or(&0) as u32,
            )?;

            if let GeneralizedTimeZone::UTC = t.time_zone {
                naive.and_utc()
            } else {
                return Option::None;
            }
        }
    };

    Option::Some(dt.timestamp())
}

#[allow(unused_macros)]
macro_rules! count_args {
    () => { 0 };
    ($x:expr $(, $rest:expr)*) => { 1 + count_args!($($rest),*) };
}
pub(crate) use count_args;

#[allow(unused_macros)]
macro_rules! spec_app {
    ($name:literal $(, $args:expr)* $(,)?) => {
        ::builtin_macros::verus_proof_expr! {
            SpecTerm::App(
                SpecFnName::User($name.view(), count_args!($($args),*) as int),
                seq![$($args),*],
            )
        }
    };
}
pub(crate) use spec_app;

#[allow(unused_macros)]
macro_rules! spec_fact {
    ($name:literal $(, $args:expr)* $(,)?) => {
        ::builtin_macros::verus_proof_expr! {
            SpecRule {
                head: spec_app!($name $(, $args)*),
                body: seq![],
            }
        }
    }
}
pub(crate) use spec_fact;

/// String literal as a SpecTerm
#[allow(unused_macros)]
macro_rules! spec_str {
    ($x:expr) => {
        ::builtin_macros::verus_proof_expr! {
            SpecTerm::Literal(SpecLiteral::String($x))
        }
    };
}
pub(crate) use spec_str;

/// Atom literal as a SpecTerm
#[allow(unused_macros)]
macro_rules! spec_atom {
    ($x:expr) => {
        ::builtin_macros::verus_proof_expr! {
            SpecTerm::Literal(SpecLiteral::Atom($x))
        }
    };
}
pub(crate) use spec_atom;

/// String literal as a SpecTerm
#[allow(unused_macros)]
macro_rules! spec_int {
    ($x:expr) => {
        ::builtin_macros::verus_proof_expr! {
            SpecTerm::Literal(SpecLiteral::Int($x))
        }
    };
}
pub(crate) use spec_int;

}
