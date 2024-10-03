// Specifications for some base operations on X.509 certificates
// e.g. comparing distinguished names, checking issuers

use vstd::prelude::*;

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
    let facts =
        Seq::new(chain.len(), |i| spec_gen_cert_facts(chain[i], i)) +
        Seq::new(roots.len(), |i| spec_gen_cert_facts(roots[i], i + chain.len())) +
        seq![ seq![ spec_domain_fact(domain) ] ];

    facts.flatten() + spec_gen_root_issue_facts(roots, chain) + spec_gen_chain_issue_facts(chain)
}

/// Generate facts about root certs issuing chain certs
pub open spec fn spec_gen_root_issue_facts(
    roots: Seq<SpecCertificateValue>,
    chain: Seq<SpecCertificateValue>,
) -> Seq<SpecRule>
{
    Seq::new(roots.len(),
        |i| Seq::new(chain.len(), |j|
            if spec_likely_issued(roots[i], chain[j]) &&
                spec_verify_signature(roots[i], chain[j]) {
                seq![ spec_issuer_fact(i + chain.len(), j) ]
            } else {
                seq![]
            }
        ).flatten()
    ).flatten()
}

/// Generate facts about chain certs issuing each other
pub open spec fn spec_gen_chain_issue_facts(
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
pub open spec fn spec_get_extension_param(cert: SpecCertificateValue, oid: SpecObjectIdentifierValue) -> OptionDeep<SpecExtensionParamValue>
{
    if let Some(exts) = cert.cert.extensions {
        spec_get_extension_param_helper(exts, oid)
    } else {
        None
    }
}

pub open spec fn spec_get_extension_param_helper(exts: Seq<SpecExtensionValue>, oid: SpecObjectIdentifierValue) -> OptionDeep<SpecExtensionParamValue>
    decreases exts.len()
{
    if exts.len() == 0 {
        None
    } else {
        if exts[0].id =~= oid {
            Some(exts[0].param)
        } else {
            spec_get_extension_param_helper(exts.drop_first(), oid)
        }
    }
}

/// Get the AuthorityKeyIdentifier extension if it exists
pub open spec fn spec_get_auth_key_id(cert: SpecCertificateValue) -> OptionDeep<SpecAuthorityKeyIdentifierValue>
{
    if let Some(param) = spec_get_extension_param(cert, spec_oid!(2, 5, 29, 35)) {
        if let SpecExtensionParamValue::AuthorityKeyIdentifier(param) = param {
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
    if let Some(param) = spec_get_extension_param(cert, spec_oid!(2, 5, 29, 14)) {
        if let SpecExtensionParamValue::SubjectKeyIdentifier(param) = param {
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
    ]
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
        SpecTerm::Literal(SpecLiteral::String($x))
    };
}
pub(crate) use spec_str;

/// String literal as a SpecTerm
#[allow(unused_macros)]
macro_rules! spec_int {
    ($x:expr) => {
        SpecTerm::Literal(SpecLiteral::Int($x))
    };
}
pub(crate) use spec_int;

}
