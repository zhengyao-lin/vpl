// Specifications for some base operations on X.509 certificates
// e.g. comparing distinguished names, checking issuers

use vstd::prelude::*;

use polyfill::*;

use parser::asn1::*;
use parser::common::*;
use parser::x509::*;

use parser::common::OptionDeep::*;

use vpl::proof::*;

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
    let merged_policy = spec_merge_policy_facts(policy, roots, chain, domain);

    &&& chain.len() > 0

    // Exists a proof of the final goal certVerifiedChain(cert(0))
    &&& exists |thm: SpecTheorem| {
        &&& #[trigger] thm.wf(merged_policy)
        &&& thm.stmt == SpecTerm::App(
            SpecFnName::User("certVerifiedChain"@, 1),
            seq![ spec_cert_id_term(0) ],
        )
    }
}

/// Merge the policy with facts about each certificate,
/// issuer relation between certificates, and environment
/// facts such as the domain to be validated
pub open spec fn spec_merge_policy_facts(
    policy: SpecProgram,
    roots: Seq<SpecCertificateValue>,
    chain: Seq<SpecCertificateValue>,
    domain: SpecStringLiteral,
) -> SpecProgram
{
    let facts =
        Seq::new(chain.len(), |i| spec_cert_to_facts(chain[i], i)) +
        Seq::new(roots.len(), |i| spec_cert_to_facts(roots[i], i + chain.len())) +
        seq![ seq![ spec_domain_fact(domain) ] ] +

        // Facts about whether any root cert issued any of the chain certs
        Seq::new(roots.len(),
            |i| Seq::new(chain.len(), |j|
                if spec_likely_issued(roots[i], chain[j]) &&
                    spec_verify_signature(roots[i], chain[j]) {
                    seq![ spec_issuer_fact(i + chain.len(), j) ]
                } else {
                    seq![]
                }
            ).flatten()
        ) +

        // Facts about the chain[i] being issued by chain[i + 1]
        Seq::new((chain.len() - 1) as nat,
            |i: int| if spec_likely_issued(chain[i + 1], chain[i]) &&
                spec_verify_signature(chain[i + 1], chain[i]) {
                seq![ spec_issuer_fact(i + 1, i) ]
            } else {
                seq![]
            }
        );

    SpecProgram { rules: policy.rules + facts.flatten() }
}

/// Construct an issuer fact of the form issuer(cert_i, cert_j)
/// NOTE: i is the issuer of j
pub open spec fn spec_issuer_fact(i: int, j: int) -> SpecRule
{
    SpecRule {
        head: SpecTerm::App(
            SpecFnName::User("issuer"@, 2),
            seq![ spec_cert_id_term(j), spec_cert_id_term(i) ],
        ),
        body: seq![],
    }
}

/// Construct envDomain(domain)
pub open spec fn spec_domain_fact(domain: SpecStringLiteral) -> SpecRule
{
    SpecRule {
        head: SpecTerm::App(
            SpecFnName::User("envDomain"@, 1),
            seq![ SpecTerm::Literal(SpecLiteral::String(domain)) ],
        ),
        body: seq![],
    }
}

/// Construct term cert(i)
pub open spec fn spec_cert_id_term(i: int) -> SpecTerm
{
    // NOTE: instead of doing cert_i as in the original Hammurabi
    // we use cert(i) to avoid int::to_string in the spec
    SpecTerm::App(
        SpecFnName::User("cert"@, 1),
        seq![ SpecTerm::Literal(SpecLiteral::Int(i)) ],
    )
}

/// Specify the facts to be generated from a certificate
pub open spec fn spec_cert_to_facts(cert: SpecCertificateValue, i: int) -> Seq<SpecRule>
{
    // TODO
    seq![]
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
/// Basically compare the equality, except that two PrintableString's
/// are considered equal modulo upper/lower case, leading/trailing white spaces
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

//// Implementations of the specs above

pub fn likely_issued(issuer: &CertificateValue, subject: &CertificateValue) -> (res: bool)
    ensures res == spec_likely_issued(issuer@, subject@)
{
    same_name(&issuer.cert.subject, &subject.cert.issuer) &&
    check_auth_key_id(issuer, subject)
}

pub fn check_auth_key_id(issuer: &CertificateValue, subject: &CertificateValue) -> (res: bool)
    ensures res == spec_check_auth_key_id(issuer@, subject@)
{
    if let Some(akid) = get_auth_key_id(subject) {
        // Check key id
        if let Some(key_id) = &akid.key_id {
            if let Some(skid) = get_subject_key_id(issuer) {
                assert(akid@.key_id matches OptionDeep::Some(id) && spec_get_subject_key_id(issuer@) matches Some(skid));
                if !key_id.polyfill_eq(&skid) {
                    return false;
                }

                assert(akid@.key_id matches OptionDeep::Some(id) && spec_get_subject_key_id(issuer@) matches Some(skid) && id == skid);
            }
        }

        // Check serial number
        if let Some(serial) = &akid.auth_cert_serial {
            if !serial.polyfill_eq(&issuer.cert.serial) {
                return false;
            }
        }

        return true;
    }

    true
}

pub fn get_extension_param<'a, 'b>(cert: &'b CertificateValue<'a>, oid: &ObjectIdentifierValue) -> (res: OptionDeep<&'b ExtensionParamValue<'a>>)
    ensures res@ == spec_get_extension_param(cert@, oid@)
{
    if let Some(exts) = &cert.cert.extensions {
        let len = exts.len();

        assert(exts@.skip(0) == exts@);

        for i in 0..len
            invariant
                len == exts@.len(),
                forall |j| #![auto] 0 <= j < i ==> exts@[j].id != oid@,
                spec_get_extension_param(cert@, oid@)
                    == spec_get_extension_param_helper(exts@.skip(i as int), oid@),
        {
            if exts.get(i).id.polyfill_eq(oid) {
                return Some(&exts.get(i).param);
            }

            assert(exts@.skip(i as int).drop_first() == exts@.skip(i + 1));
        }

        None
    } else {
        None
    }
}

pub fn get_auth_key_id<'a, 'b>(cert: &'b CertificateValue<'a>) -> (res: OptionDeep<&'b AuthorityKeyIdentifierValue<'a>>)
    ensures res@ == spec_get_auth_key_id(cert@)
{
    let oid = oid!(2, 5, 29, 35);
    assert(oid@ == spec_oid!(2, 5, 29, 35));

    if let Some(param) = get_extension_param(cert, &oid) {
        if let ExtensionParamValue::AuthorityKeyIdentifier(param) = param {
            return Some(param);
        }
    }

    None
}

pub fn get_subject_key_id<'a, 'b>(cert: &'b CertificateValue<'a>) -> (res: OptionDeep<&'b [u8]>)
    ensures res@ == spec_get_subject_key_id(cert@)
{
    let oid = oid!(2, 5, 29, 14);
    assert(oid@ == spec_oid!(2, 5, 29, 14));

    if let Some(param) = get_extension_param(cert, &oid) {
        if let ExtensionParamValue::SubjectKeyIdentifier(param) = param {
            return Some(param);
        }
    }

    None
}

pub fn same_name(a: &NameValue, b: &NameValue) -> (res: bool)
    ensures res == spec_same_name(a@, b@)
{
    if a.len() != b.len() {
        return false;
    }

    let len = a.len();
    for i in 0..len
        invariant
            len == a@.len(),
            a@.len() == b@.len(),
            forall |j| #![auto] 0 <= j < i ==> spec_same_rdn(a@[j], b@[j]),
    {
        if !same_rdn(a.get(i), b.get(i)) {
            return false;
        }
    }

    true
}

pub fn same_rdn(a: &RDNValue, b: &RDNValue) -> (res: bool)
    ensures res == spec_same_rdn(a@, b@)
{
    if a.len() != b.len() {
        return false;
    }

    let len = a.len();
    for i in 0..len
        invariant
            len == a@.len(),
            a@.len() == b@.len(),
            forall |j| #![auto] 0 <= j < i ==> spec_same_attr(a@[j], b@[j]),
    {
        if !same_attr(a.get(i), b.get(i)) {
            return false;
        }
    }

    true
}

pub fn same_attr(a: &AttributeTypeAndValueValue, b: &AttributeTypeAndValueValue) -> (res: bool)
    ensures res == spec_same_attr(a@, b@)
{
    a.typ.polyfill_eq(&b.typ) && match (&a.value, &b.value) {
        (DirectoryStringValue::PrintableString(a), DirectoryStringValue::PrintableString(b)) |
        (DirectoryStringValue::UTF8String(a), DirectoryStringValue::UTF8String(b)) |
        (DirectoryStringValue::IA5String(a), DirectoryStringValue::IA5String(b)) =>
            str_eq_str(a, b),

        (DirectoryStringValue::TeletexString(a), DirectoryStringValue::TeletexString(b)) |
        (DirectoryStringValue::BMPString(a), DirectoryStringValue::BMPString(b)) |
        (DirectoryStringValue::UniversalString(a), DirectoryStringValue::UniversalString(b)) =>
            a.polyfill_eq(b),

        _ => false,
    }
}

}
