use vstd::prelude::*;

use polyfill::*;

use parser::{*, asn1::*, x509::*};
use parser::OptionDeep::*;

use vpl::*;
use crate::specs::*;
use crate::hash;

verus! {

#[derive(Debug)]
pub enum ValidationError {
    IntegerOverflow,
    EmptyChain,
    ProofFailure,
}

pub fn likely_issued(issuer: &CertificateValue, subject: &CertificateValue) -> (res: bool)
    ensures res == spec_likely_issued(issuer@, subject@)
{
    same_name(&issuer.get().cert.get().subject, &subject.get().cert.get().issuer) &&
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
            if !serial.polyfill_eq(&issuer.get().cert.get().serial) {
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
    if let Some(exts) = &cert.get().cert.get().extensions {
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
    subject.get().sig_alg.polyfill_eq(&subject.get().cert.get().signature)
}

pub fn gen_cert_facts(cert: &CertificateValue, i: LiteralInt) -> (res: Result<VecDeep<Rule>, ValidationError>)
    ensures res matches Ok(res) ==> res@ =~~= spec_gen_cert_facts(cert@, i as int)
{
    let ser_cert = cert.serialize();

    let fingerprint = RuleX::new(
        TermX::app_str("fingerprint", vec![
            cert_name(i),
            TermX::str(hash::to_hex_upper(&hash::sha256_digest(ser_cert)).as_str()),
        ]),
        vec![],
    );
    let ghost fingerprint_view = spec_fact!("fingerprint",
        spec_cert_name(i as int),
        spec_str!(hash::spec_to_hex_upper(hash::spec_sha256_digest(ASN1(CertificateInner).view().spec_serialize(cert.view()).unwrap()))),
    );

    assert(fingerprint@.head->App_1 == fingerprint_view.head->App_1);

    Ok(vec_deep![ fingerprint ])
}

pub fn issuer_fact(i: LiteralInt, j: LiteralInt) -> (res: Rule)
    ensures res@ =~= spec_issuer_fact(i as int, j as int)
{
    let res = RuleX::new(
        TermX::app_str("issuer", vec![ cert_name(j), cert_name(i) ]),
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

pub fn cert_name(i: LiteralInt) -> (res: Term)
    ensures res@ =~= spec_cert_name(i as int)
{
    let res = TermX::app_str("cert", vec![ TermX::int(i) ]);
    assert(res@->App_1 == spec_cert_name(i as int)->App_1);
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
            facts.push(gen_cert_facts(chain.get(i), i as LiteralInt)?);
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
                facts.push(gen_cert_facts(roots.get(i), sum as LiteralInt)?);
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
    debug: bool,
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

    if debug {
        eprintln_join!("[debug] facts:");
        for i in 0..facts.len() {
            eprintln_join!("  - ", &facts[i]);
        }
    }

    policy.rules.append(&mut facts);

    let goal = TermX::app_str("certVerifiedChain", vec![ cert_name(0) ]);
    assert(goal@->App_1 == seq![ spec_cert_name(0) ]);

    // Solve and validate the goal
    match solve_and_validate::<B, E>(backend, &policy, &goal, debug, true)? {
        ValidationResult::Success(thm) => {
            assert(policy@ =~= SpecProgram {
                rules: old_policy.rules + spec_gen_all_facts(roots@, chain@, domain@),
            });
            Ok(true)
        }
        ValidationResult::ProofFailure => Err(ValidationError::ProofFailure)?,
        ValidationResult::BackendFailure => Ok(false),
    }
}

}
