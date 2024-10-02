// Specifications for some base operations on X.509 certificates
// e.g. comparing distinguished names, checking issuers

use vstd::prelude::*;

use polyfill::*;

use parser::asn1::*;
use parser::common::*;
use parser::x509::*;

use parser::common::OptionDeep::*;

use vpl::checker::*;
use vpl::proof::*;
use vpl::backend::*;
use vpl::validate::*;

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
        &&& thm.stmt == SpecTerm::App(
            SpecFnName::User("certVerifiedChain"@, 1),
            seq![ spec_cert_id_term(0) ],
        )
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
pub closed spec fn spec_gen_cert_facts(cert: SpecCertificateValue, i: int) -> Seq<SpecRule>;

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

pub enum ValidationError {
    IntegerOverflow,
    EmptyChain,
    ProofFailure,
}

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

pub fn verify_signature(issuer: &CertificateValue, subject: &CertificateValue) -> (res: bool)
    ensures res == spec_verify_signature(issuer@, subject@)
{
    // TODO: verify signature
    subject.sig_alg.polyfill_eq(&subject.cert.signature)
}

#[verifier::external_body]
pub fn gen_cert_facts(cert: &CertificateValue, i: LiteralInt) -> (res: VecDeep<Rule>)
    ensures res@ =~= spec_gen_cert_facts(cert@, i as int)
{
    // TODO
    vec_deep![]
}

pub fn issuer_fact(i: LiteralInt, j: LiteralInt) -> (res: Rule)
    ensures res@ =~= spec_issuer_fact(i as int, j as int)
{
    let res = RuleX::new(
        TermX::app_str("issuer", vec![ cert_id_term(j), cert_id_term(i) ]),
        vec![],
    );
    assert(res@.head->App_1 == spec_issuer_fact(i as int, j as int).head->App_1);
    res
}

pub fn domain_fact(domain: &str) -> (res: Rule)
    ensures res@ =~= spec_domain_fact(domain@)
{
    let res = RuleX::new(
        TermX::app_str("envDomain", vec![ TermX::str(domain) ]),
        vec![],
    );
    assert(res@.head->App_1 == spec_domain_fact(domain@).head->App_1);
    res
}

pub fn cert_id_term(i: LiteralInt) -> (res: Term)
    ensures res@ =~= spec_cert_id_term(i as int)
{
    let res = TermX::app_str("cert", vec![ TermX::int(i) ]);
    assert(res@->App_1 == spec_cert_id_term(i as int)->App_1);
    res
}

pub fn gen_root_issue_facts(
    roots: &VecDeep<CertificateValue>,
    chain: &VecDeep<CertificateValue>,
) -> (res: Result<VecDeep<Rule>, ValidationError>)
    ensures
        res matches Ok(res) ==>
            res@ =~= spec_gen_root_issue_facts(roots@, chain@)
{
    let mut facts = vec_deep![];
    let chain_len = chain.len();
    let roots_len = roots.len();

    for i in 0..roots_len
        invariant
            chain_len == chain@.len(),
            roots_len == roots@.len(),

            facts@ =~=
                Seq::new(i as nat,
                    |i| Seq::new(chain@.len(), |j|
                        if spec_likely_issued(roots@[i], chain@[j]) &&
                            spec_verify_signature(roots@[i], chain@[j]) {
                            seq![ spec_issuer_fact(i + chain@.len(), j) ]
                        } else {
                            seq![]
                        }
                    ).flatten()
                ),
    {
        let mut issuer_facts = vec_deep![];

        for j in 0..chain_len
            invariant
                0 <= i < roots_len,
                chain_len == chain@.len(),
                roots_len == roots@.len(),

                issuer_facts@ =~~=
                    Seq::new(j as nat, |j|
                        if spec_likely_issued(roots@[i as int], chain@[j as int]) &&
                            spec_verify_signature(roots@[i as int], chain@[j as int]) {
                            seq![ spec_issuer_fact(i + chain@.len(), j) ]
                        } else {
                            seq![]
                        }
                    ),
        {
            // Verify signature too
            if likely_issued(roots.get(i), chain.get(j)) &&
                verify_signature(roots.get(i), chain.get(j)) {
                // Check bounds and overflow
                if let Option::Some(root_id) = i.checked_add(chain.len()) {
                    if root_id > LiteralInt::MAX as usize || j > LiteralInt::MAX as usize {
                        return Err(ValidationError::IntegerOverflow);
                    }

                    issuer_facts.push(vec_deep![
                        issuer_fact(root_id as LiteralInt, j as LiteralInt)
                    ]);
                } else {
                    return Err(ValidationError::IntegerOverflow);
                }
            } else {
                issuer_facts.push(vec_deep![]);
            }
        }

        facts.push(VecDeep::flatten(issuer_facts));
    }

    Ok(VecDeep::flatten(facts))
}

pub fn gen_chain_issue_facts(
    chain: &VecDeep<CertificateValue>,
) -> (res: Result<VecDeep<Rule>, ValidationError>)
    requires chain@.len() > 0
    ensures res matches Ok(res) ==>
        res@ =~= spec_gen_chain_issue_facts(chain@)
{
    let mut facts = vec_deep![];
    let chain_len = chain.len();

    // Add facts about the (i + 1)-th certificate issuing the i-th certificate
    for i in 0..chain_len - 1
        invariant
            chain_len > 0,
            chain_len == chain@.len(),
            facts@ =~~= Seq::new(i as nat,
                    |i: int| if spec_likely_issued(chain@[i + 1], chain@[i]) &&
                        spec_verify_signature(chain@[i + 1], chain@[i]) {
                        seq![ spec_issuer_fact(i + 1, i) ]
                    } else {
                        seq![]
                    }
                ),
    {
        if likely_issued(chain.get(i + 1), chain.get(i)) &&
            verify_signature(chain.get(i + 1), chain.get(i)) {
            if i >= LiteralInt::MAX as usize {
                return Err(ValidationError::IntegerOverflow);
            }

            facts.push(vec_deep![ issuer_fact(i as LiteralInt + 1, i as LiteralInt) ]);
        } else {
            facts.push(vec_deep![]);
        }
    }

    Ok(VecDeep::flatten(facts))
}

pub fn gen_all_facts(
    roots: &VecDeep<CertificateValue>,
    chain: &VecDeep<CertificateValue>,
    domain: &str,
) -> (res: Result<VecDeep<Rule>, ValidationError>)
    requires chain@.len() > 0
    ensures res matches Ok(res) ==>
        res@ =~= spec_gen_all_facts(roots@, chain@, domain@)
{
    let mut facts: VecDeep<VecDeep<Rule>> = vec_deep![];
    let chain_len = chain.len();
    let roots_len = roots.len();

    // Push chain cert facts
    for i in 0..chain_len
        invariant
            chain_len == chain@.len(),
            roots_len == roots@.len(),
            facts@ =~= Seq::new(i as nat, |i| spec_gen_cert_facts(chain@[i], i)),
    {
        if i <= LiteralInt::MAX as usize {
            facts.push(gen_cert_facts(chain.get(i), i as LiteralInt));
        } else {
            return Err(ValidationError::IntegerOverflow);
        }
    }

    // Push root cert facts
    for i in 0..roots_len
        invariant
            chain_len == chain@.len(),
            roots_len == roots@.len(),
            facts@ =~=
                Seq::new(chain@.len(), |i| spec_gen_cert_facts(chain@[i], i)) +
                Seq::new(i as nat, |i| spec_gen_cert_facts(roots@[i], i + chain@.len())),
    {
        if let Option::Some(sum) = i.checked_add(chain.len()) {
            if sum <= LiteralInt::MAX as usize {
                facts.push(gen_cert_facts(roots.get(i), sum as LiteralInt));
            } else {
                return Err(ValidationError::IntegerOverflow);
            }
        } else {
            return Err(ValidationError::IntegerOverflow);
        }
    }

    facts.push(vec_deep![ domain_fact(domain) ]);

    assert(facts@ =~~=
        Seq::new(chain@.len(), |i| spec_gen_cert_facts(chain@[i], i)) +
        Seq::new(roots@.len(), |i| spec_gen_cert_facts(roots@[i], i + chain@.len())) +
        seq![ seq![ spec_domain_fact(domain@) ] ]);

    let mut facts = VecDeep::flatten(facts);

    let mut root_issuers = gen_root_issue_facts(roots, chain)?;
    let mut chain_issuers = gen_chain_issue_facts(chain)?;

    facts.append(&mut root_issuers);
    facts.append(&mut chain_issuers);

    Ok(facts)
}

pub fn valid_domain<B: Backend, E>(
    backend: &mut B,
    mut policy: Program,
    roots: &VecDeep<CertificateValue>,
    chain: &VecDeep<CertificateValue>,
    domain: &str,
) -> (res: Result<bool, E>)
    where
        E: std::convert::From<B::Error>,
        E: std::convert::From<ValidationError>,
        E: std::convert::From<ProofError>,

    ensures
        res matches Ok(true) ==> spec_valid_domain(policy@, roots@, chain@, domain@),
{
    if chain.len() == 0 {
        Err(ValidationError::EmptyChain)?;
    }

    let ghost old_policy = policy@;

    // Add all generated facts to the policy
    let mut facts = gen_all_facts(roots, chain, domain)?.to_vec();
    policy.rules.append(&mut facts);

    let goal = TermX::app_str("certVerifiedChain", vec![ cert_id_term(0) ]);
    assert(goal@->App_1 == seq![ spec_cert_id_term(0) ]);

    // Solve and validate the goal
    match solve_and_validate::<B, E>(backend, &policy, &goal, true, true)? {
        ValidateResult::Success(thm) => {
            assert(policy@ =~= SpecProgram {
                rules: old_policy.rules + spec_gen_all_facts(roots@, chain@, domain@),
            });
            Ok(true)
        }
        ValidateResult::ProofFailure => Err(ValidationError::ProofFailure)?,
        ValidateResult::BackendFailure => Ok(false),
    }
}

}
