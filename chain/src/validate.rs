use vstd::prelude::*;

use polyfill::*;

use parser::{*, asn1::*, x509::*};
use parser::OptionDeep::*;

use vpl::*;
use crate::specs::*;
use crate::hash;

verus! {

broadcast use vpl::lemma_ext_equal_deep;

#[derive(Debug)]
pub enum ValidationError {
    IntegerOverflow,
    EmptyChain,
    ProofFailure,
    TimeParseError,
    RSAPubKeyParseError,
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

pub fn dir_string_to_string<'a, 'b>(dir: &'b DirectoryStringValue<'a>) -> (res: OptionDeep<&'a str>)
    ensures res@ == spec_dir_string_to_string(dir@)
{
    match dir {
        DirectoryStringValue::PrintableString(s) => Some(s),
        DirectoryStringValue::UTF8String(s) => Some(s),
        DirectoryStringValue::IA5String(s) => Some(s),
        DirectoryStringValue::TeletexString(s) => None,
        DirectoryStringValue::UniversalString(s) => None,
        DirectoryStringValue::BMPString(s) => None,
    }
}

/// Get RDN value of a specific OID
pub fn get_rdn<'a, 'b>(name: &'b NameValue<'a>, oid: &'b ObjectIdentifierValue) -> (res: OptionDeep<&'a str>)
    ensures res@ == spec_get_rdn(name@, oid@)
{
    let len = name.len();

    assert(name@.skip(0) == name@);

    for i in 0..len
        invariant
            len == name@.len(),
            spec_get_rdn(name@, oid@) =~= spec_get_rdn(name@.skip(i as int), oid@),
    {
        if name.get(i).len() == 1 && name.get(i).get(0).typ.polyfill_eq(oid) {
            return dir_string_to_string(&name.get(i).get(0).value);
        }
        assert(name@.skip(i as int).drop_first() == name@.skip(i + 1));
    }

    return None;
}

pub fn oid_to_str(oid: &ObjectIdentifierValue) -> (res: String)
    ensures res@ =~= spec_oid_to_str(oid@)
{
    let strings = vec_map(oid.0.to_vec(),
        |id: &u64| -> (res: String)
        ensures res@ == spec_u64_to_string(*id)
        { u64_to_string(*id) });

    assert(Seq::new(strings@.len(), |i| strings@[i]@) =~= Seq::new(oid@.len(), |i| spec_u64_to_string(oid@[i])));
    assert(Seq::new(strings@.len(), |i| strings@[i]@) =~= strings@.map_values(|v: String| v@));

    join_strings(&strings, ".")
}

pub fn gen_cert_facts(cert: &CertificateValue, i: LiteralInt) -> (res: Result<VecDeep<Rule>, ValidationError>)
    ensures res matches Ok(res) ==> res@ =~~= spec_gen_cert_facts(cert@, i as int)
{
    let ser_cert = cert.serialize();

    let mut facts = gen_subject_name_info(cert, i)?;
    let mut rest = vec_deep![
        RuleX::fact("fingerprint", vec![
            cert_name(i),
            TermX::str(hash::to_hex_upper(&hash::sha256_digest(ser_cert)).as_str()),
        ]),

        RuleX::fact("version", vec![ cert_name(i), TermX::int(cert.get().cert.get().version) ]),

        RuleX::fact("signatureAlgorithm", vec![
            cert_name(i),
            TermX::str(oid_to_str(&cert.get().sig_alg.id).as_str()),
        ]),

        RuleX::fact("notAfter", vec![
            cert_name(i),
            TermX::int(x509_time_to_timestamp(&cert.get().cert.get().validity.not_after).ok_or(ValidationError::TimeParseError)?),
        ]),

        RuleX::fact("notBefore", vec![
            cert_name(i),
            TermX::int(x509_time_to_timestamp(&cert.get().cert.get().validity.not_before).ok_or(ValidationError::TimeParseError)?),
        ]),

        gen_spki_dsa_param_fact(cert, i)?,
        gen_spki_rsa_param_fact(cert, i)?,
    ];

    facts.append(&mut rest);

    Ok(facts)
}

pub fn gen_subject_name_info(cert: &CertificateValue, i: LiteralInt) -> (res: Result<VecDeep<Rule>, ValidationError>)
    ensures res matches Ok(res) ==> res@ =~~= spec_gen_subject_name_info(cert@, i as int)
{
    let oid = oid!(2, 5, 4, 3); assert(oid@ == spec_oid!(2, 5, 4, 3));
    let oid = oid!(2, 5, 4, 4); assert(oid@ == spec_oid!(2, 5, 4, 4));
    let oid = oid!(2, 5, 4, 6); assert(oid@ == spec_oid!(2, 5, 4, 6));
    let oid = oid!(2, 5, 4, 7); assert(oid@ == spec_oid!(2, 5, 4, 7));
    let oid = oid!(2, 5, 4, 8); assert(oid@ == spec_oid!(2, 5, 4, 8));
    let oid = oid!(2, 5, 4, 9); assert(oid@ == spec_oid!(2, 5, 4, 9));
    let oid = oid!(2, 5, 4, 10); assert(oid@ == spec_oid!(2, 5, 4, 10));
    let oid = oid!(2, 5, 4, 42); assert(oid@ == spec_oid!(2, 5, 4, 42));
    let oid = oid!(2, 5, 4, 17); assert(oid@ == spec_oid!(2, 5, 4, 17));

    Ok(vec_deep![
        // TODO: performance?
        RuleX::fact("subject", vec![
            cert_name(i),
            TermX::str(get_rdn(&cert.get().cert.get().subject, &oid!(2, 5, 4, 3)).unwrap_or("")),
            TermX::str(get_rdn(&cert.get().cert.get().subject, &oid!(2, 5, 4, 6)).unwrap_or("")),
            TermX::str(get_rdn(&cert.get().cert.get().subject, &oid!(2, 5, 4, 7)).unwrap_or("")),
            TermX::str(get_rdn(&cert.get().cert.get().subject, &oid!(2, 5, 4, 8)).unwrap_or("")),
            TermX::str(get_rdn(&cert.get().cert.get().subject, &oid!(2, 5, 4, 10)).unwrap_or("")),
        ]),

        RuleX::fact("commonName", vec![
            cert_name(i),
            TermX::str(get_rdn(&cert.get().cert.get().subject, &oid!(2, 5, 4, 3)).unwrap_or("")),
        ]),

        RuleX::fact("country", vec![
            cert_name(i),
            TermX::str(get_rdn(&cert.get().cert.get().subject, &oid!(2, 5, 4, 6)).unwrap_or("")),
        ]),

        RuleX::fact("givenName", vec![
            cert_name(i),
            TermX::str(get_rdn(&cert.get().cert.get().subject, &oid!(2, 5, 4, 42)).unwrap_or("")),
        ]),

        RuleX::fact("localityName", vec![
            cert_name(i),
            TermX::str(get_rdn(&cert.get().cert.get().subject, &oid!(2, 5, 4, 7)).unwrap_or("")),
        ]),

        RuleX::fact("organizationName", vec![
            cert_name(i),
            TermX::str(get_rdn(&cert.get().cert.get().subject, &oid!(2, 5, 4, 10)).unwrap_or("")),
        ]),

        RuleX::fact("postalCode", vec![
            cert_name(i),
            TermX::str(get_rdn(&cert.get().cert.get().subject, &oid!(2, 5, 4, 17)).unwrap_or("")),
        ]),

        RuleX::fact("stateOrProvinceName", vec![
            cert_name(i),
            TermX::str(get_rdn(&cert.get().cert.get().subject, &oid!(2, 5, 4, 8)).unwrap_or("")),
        ]),

        RuleX::fact("streetAddress", vec![
            cert_name(i),
            TermX::str(get_rdn(&cert.get().cert.get().subject, &oid!(2, 5, 4, 9)).unwrap_or("")),
        ]),

        RuleX::fact("surname", vec![
            cert_name(i),
            TermX::str(get_rdn(&cert.get().cert.get().subject, &oid!(2, 5, 4, 4)).unwrap_or("")),
        ]),
    ])
}

pub fn gen_spki_dsa_param_fact(cert: &CertificateValue, i: LiteralInt) -> (res: Result<Rule, ValidationError>)
    ensures res matches Ok(res) ==> res@ =~~= spec_gen_spki_dsa_param_fact(cert@, i as int)
{
    match &cert.get().cert.get().subject_key.alg.param {
        AlgorithmParamValue::DSASignature(Either::Left(param)) => {
            let p_len = param.p.byte_len();
            let q_len = param.q.byte_len();
            let g_len = param.g.byte_len();

            if p_len > LiteralInt::MAX as usize / 8 || q_len > LiteralInt::MAX as usize / 8 || g_len > LiteralInt::MAX as usize / 8 {
                return Err(ValidationError::IntegerOverflow);
            }

            Ok(RuleX::fact("spkiDSAParam", vec![
                cert_name(i),
                TermX::int((p_len * 8) as LiteralInt),
                TermX::int((q_len * 8) as LiteralInt),
                TermX::int((g_len * 8) as LiteralInt),
            ]))
        }

        _ => Ok(RuleX::fact("spkiDSAParam", vec![
            cert_name(i),
            TermX::atom("na"),
            TermX::atom("na"),
            TermX::atom("na"),
        ])),
    }
}

pub fn gen_spki_rsa_param_fact(cert: &CertificateValue, i: LiteralInt) -> (res: Result<Rule, ValidationError>)
    ensures res matches Ok(res) ==> res@ =~~= spec_gen_spki_rsa_param_fact(cert@, i as int)
{
    match &cert.get().cert.get().subject_key.alg.param {
        AlgorithmParamValue::RSAEncryption(..) => {
            let pub_key = cert.get().cert.get().subject_key.pub_key.bytes();
            let parsed = match ASN1(RSAParam).parse(pub_key) {
                Ok((_, parsed)) => parsed,
                Err(_) => return Err(ValidationError::RSAPubKeyParseError),
            };

            let mod_len = parsed.modulus.byte_len();

            if mod_len > LiteralInt::MAX as usize / 8 {
                return Err(ValidationError::IntegerOverflow);
            }

            Ok(RuleX::fact("spkiRSAModLength", vec![
                cert_name(i),
                TermX::int((mod_len * 8) as LiteralInt),
            ]))
        }

        _ => Ok(RuleX::fact("spkiRSAModLength", vec![ cert_name(i), TermX::atom("na") ])),
    }
}

pub fn issuer_fact(i: LiteralInt, j: LiteralInt) -> (res: Rule)
    ensures res@ =~~= spec_issuer_fact(i as int, j as int)
{
    RuleX::fact("issuer", vec![ cert_name(j), cert_name(i) ])
}

pub fn domain_fact(domain: &str) -> (res: Rule)
    ensures res@ =~~= spec_domain_fact(domain@)
{
    RuleX::fact("envDomain", vec![ TermX::str(domain) ])
}

pub fn cert_name(i: LiteralInt) -> (res: Term)
    ensures res@ =~~= spec_cert_name(i as int)
{
    TermX::app_str("cert", vec![ TermX::int(i) ])
}

/// Generate facts about root certificates and prune
/// out unused root certs
pub fn gen_root_facts(
    roots: &VecDeep<CertificateValue>,
    chain: &VecDeep<CertificateValue>,
) -> (res: Result<VecDeep<Rule>, ValidationError>)
    ensures
        res matches Ok(res) ==>
            res@ =~= spec_gen_root_facts(roots@, chain@)
{
    let mut facts = vec_deep![];
    let chain_len = chain.len();
    let roots_len = roots.len();

    for i in 0..roots_len
        invariant
            chain_len == chain@.len(),
            roots_len == roots@.len(),

            // Same as in spec_gen_root_facts
            facts@ =~= Seq::new(i as nat,
                |i| {
                    let issue_facts = Seq::new(chain@.len(), |j|
                        if spec_likely_issued(roots@[i], chain@[j]) &&
                            spec_verify_signature(roots@[i], chain@[j]) {
                            seq![ spec_issuer_fact(i + chain@.len(), j) ]
                        } else {
                            seq![]
                        }
                    ).flatten();

                    if issue_facts.len() != 0 {
                        issue_facts + spec_gen_cert_facts(roots@[i as int], i + chain@.len())
                    } else {
                        issue_facts
                    }
                }
            ),
    {
        let mut issuer_facts = vec_deep![];

        // Compute the root cert id and check overflow
        let root_id = if let Option::Some(root_id) = i.checked_add(chain_len) {
            if root_id > LiteralInt::MAX as usize {
                return Err(ValidationError::IntegerOverflow);
            }
            root_id as LiteralInt
        } else {
            return Err(ValidationError::IntegerOverflow);
        };

        // Check if the root cert issued any of the chain certs
        for j in 0..chain_len
            invariant
                0 <= i < roots_len,
                chain_len == chain@.len(),
                roots_len == roots@.len(),
                root_id == i + chain@.len(),

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
                issuer_facts.push(vec_deep![
                    issuer_fact(root_id as LiteralInt, j as LiteralInt)
                ]);
            } else {
                issuer_facts.push(vec_deep![]);
            }
        }

        let mut issuer_facts = VecDeep::flatten(issuer_facts);

        if issuer_facts.len() != 0 {
            // Add the root cert iff some chain cert is issued by it
            let mut root_facts = gen_cert_facts(roots.get(i), root_id)?;
            issuer_facts.append(&mut root_facts);
        }

        facts.push(issuer_facts);
    }

    Ok(VecDeep::flatten(facts))
}

pub fn gen_chain_issuer_facts(
    chain: &VecDeep<CertificateValue>,
) -> (res: Result<VecDeep<Rule>, ValidationError>)
    requires chain@.len() > 0
    ensures res matches Ok(res) ==>
        res@ =~= spec_gen_chain_issuer_facts(chain@)
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

pub fn gen_chain_facts(
    chain: &VecDeep<CertificateValue>,
) -> (res: Result<VecDeep<Rule>, ValidationError>)
    ensures res matches Ok(res) ==>
        res@ =~= spec_gen_chain_facts(chain@)
{
    let mut facts = vec_deep![];
    let chain_len = chain.len();

    for i in 0..chain_len
        invariant
            chain_len == chain@.len(),
            facts@ =~= Seq::new(i as nat, |i| spec_gen_cert_facts(chain@[i], i)),
    {
        if i <= LiteralInt::MAX as usize {
            facts.push(gen_cert_facts(chain.get(i), i as LiteralInt)?);
        } else {
            return Err(ValidationError::IntegerOverflow);
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
    let mut facts = vec_deep![];

    let mut root_facts = gen_root_facts(roots, chain)?;
    let mut chain_issuers = gen_chain_issuer_facts(chain)?;
    let mut chain_facts = gen_chain_facts(chain)?;

    facts.append(&mut chain_issuers);
    facts.append(&mut chain_facts);
    facts.append(&mut root_facts);

    facts.push(domain_fact(domain));

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
    let mut facts = gen_all_facts(roots, chain, domain)?.to_vec_owned();

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
