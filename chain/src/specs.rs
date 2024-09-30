// Specifications for some base operations on X.509 certificates
// e.g. comparing distinguished names, checking issuers

use vstd::prelude::*;

use polyfill::*;

use parser::asn1::*;
use parser::common::*;
use parser::x509::*;

use parser::common::OptionDeep::*;

verus! {

/// If the the issuer likely issued the subject.
/// Similar to https://github.com/openssl/openssl/blob/ed6862328745c51c2afa2b6485cc3e275d543c4e/crypto/x509/v3_purp.c#L963
pub open spec fn spec_likely_issued(issuer: SpecCertificateValue, subject: SpecCertificateValue) -> bool
{
    &&& spec_same_name(issuer.tbs_certificate.subject, subject.tbs_certificate.issuer)
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
        &&& akid.auth_cert_serial matches OptionDeep::Some(serial) ==> serial =~= issuer.tbs_certificate.serial
        // TODO auth_cert_issuer
    } else {
        true
    }
}

/// Get the first extension with the given OID
pub open spec fn spec_get_extension_param(cert: SpecCertificateValue, oid: SpecObjectIdentifierValue) -> OptionDeep<SpecExtensionParamValue>
{
    if let Some(exts) = cert.tbs_certificate.extensions {
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

//// Implementations of the specs above

pub fn likely_issued(issuer: &CertificateValue, subject: &CertificateValue) -> (res: bool)
    ensures res == spec_likely_issued(issuer@, subject@)
{
    same_name(&issuer.tbs_certificate.subject, &subject.tbs_certificate.issuer) &&
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
            if !serial.polyfill_eq(&issuer.tbs_certificate.serial) {
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
    if let Some(exts) = &cert.tbs_certificate.extensions {
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
