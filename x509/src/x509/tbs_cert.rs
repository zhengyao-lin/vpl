use vstd::prelude::*;

use crate::asn1::*;
use crate::asn1::Integer;

use crate::common::*;
use super::*;

verus! {

/// TBSCertificate  ::=  SEQUENCE  {
///     version         [0]  EXPLICIT Version DEFAULT v1,
///     serialNumber         CertificateSerialNumber,
///     signature            AlgorithmIdentifier,
///     issuer               Name,
///     validity             Validity,
///     subject              Name,
///     subjectPublicKeyInfo SubjectPublicKeyInfo,
///     issuerUniqueID  [1]  IMPLICIT UniqueIdentifier OPTIONAL,
///                             -- If present, version shall be v2 or v3
///     subjectUniqueID [2]  IMPLICIT UniqueIdentifier OPTIONAL,
///                             -- If present, version shall be v2 or v3
///     extensions      [3]  EXPLICIT Extensions OPTIONAL
///                             -- If present, version shall be v3
/// }
pub type TBSCertificateInner = Mapped<
    LengthWrapped<
        Optional<ASN1<Integer>,
        Pair<ASN1<BigInt>,
        Pair<ASN1<AlgorithmIdentifier>,
        Pair<ASN1<Name>,
        Pair<ASN1<Validity>,
        Pair<ASN1<Name>,
        Pair<ASN1<PublicKeyInfo>,
        Optional<ASN1<BitString>,
        Optional<ASN1<BitString>,
        Optional<ASN1<Extensions>,
        End
    >>>>>>>>>>>,
    TBSCertificateMapper>;

wrap_combinator! {
    struct TBSCertificate: TBSCertificateInner =>
        spec SpecTBSCertificateValue,
        exec<'a> TBSCertificateValue<'a>,
        owned TBSCertificateValueOwned,
    =
        Mapped {
            inner: LengthWrapped(
                Optional(ASN1(ExplicitTag(TagValue {
                    class: TagClass::ContextSpecific,
                    form: TagForm::Constructed,
                    num: 0,
                }, ASN1(Integer))), // Version

                Pair(ASN1(BigInt), // Serial number
                Pair(ASN1(AlgorithmIdentifier), // Signature
                Pair(ASN1(Name), // Issuer
                Pair(ASN1(Validity), // Validity
                Pair(ASN1(Name), // Subject
                Pair(ASN1(PublicKeyInfo), // Subject Public Key Info

                Optional(ASN1(ImplicitTag(TagValue {
                    class: TagClass::ContextSpecific,
                    form: TagForm::Primitive,
                    num: 1,
                }, BitString)), // Issuer UID

                Optional(ASN1(ImplicitTag(TagValue {
                    class: TagClass::ContextSpecific,
                    form: TagForm::Primitive,
                    num: 2,
                }, BitString)), // Subject UID

                Optional(ASN1(ExplicitTag(TagValue {
                    class: TagClass::ContextSpecific,
                    form: TagForm::Constructed,
                    num: 3,
                }, ASN1(Extensions))), // Extensions

                End,
                ))))))))))
            ),
            mapper: TBSCertificateMapper,
        };
}

asn1_tagged!(TBSCertificate, TagValue {
    class: TagClass::Universal,
    form: TagForm::Constructed,
    num: 0x10,
});

/// TODO: maybe refactor this with a macro
#[derive(Debug, View, PolyfillClone)]
pub struct TBSCertificatePoly<
    Serial,
    AlgoId,
    Name,
    Validity,
    PubKeyInfo,
    UID,
    Extensions,
> {
    pub version: OptionDeep<IntegerValue>,
    pub serial: Serial,
    pub signature: AlgoId,
    pub issuer: Name,
    pub validity: Validity,
    pub subject: Name,
    pub subject_key: PubKeyInfo,
    pub issuer_uid: OptionDeep<UID>,
    pub subject_uid: OptionDeep<UID>,
    pub extensions: OptionDeep<Extensions>,
}

/// Different instantiations for the spec/normal/owned types
pub type SpecTBSCertificateValue = TBSCertificatePoly<
    SpecBigIntValue,
    SpecAlgorithmIdentifierValue,
    SpecNameValue,
    SpecValidityValue,
    SpecPublicKeyInfoValue,
    SpecBitStringValue,
    Seq<SpecExtensionValue>,
>;

pub type TBSCertificateValue<'a> = TBSCertificatePoly<
    BigIntValue<'a>,
    AlgorithmIdentifierValue<'a>,
    NameValue<'a>,
    ValidityValue<'a>,
    PublicKeyInfoValue<'a>,
    BitStringValue<'a>,
    VecDeep<ExtensionValue<'a>>,
>;

pub type TBSCertificateValueOwned = TBSCertificatePoly<
    BigIntOwned,
    AlgorithmIdentifierValueOwned,
    NameValueOwned,
    ValidityValueOwned,
    PublicKeyInfoValueOwned,
    BitStringValueOwned,
    VecDeep<ExtensionValueOwned>,
>;

type TBSCertificateFrom<
    Serial,
    AlgoId,
    Name,
    Validity,
    PubKeyInfo,
    UID,
    Extensions,
> = PairValue<OptionDeep<IntegerValue>,
    PairValue<Serial,
    PairValue<AlgoId,
    PairValue<Name,
    PairValue<Validity,
    PairValue<Name,
    PairValue<PubKeyInfo,
    PairValue<OptionDeep<UID>,
    PairValue<OptionDeep<UID>,
    PairValue<OptionDeep<Extensions>,
    EndValue,
    >>>>>>>>>>;

impl<
    Serial,
    AlgoId,
    Name,
    Validity,
    PubKeyInfo,
    UID,
    Extensions,
> SpecFrom<TBSCertificatePoly<
    Serial,
    AlgoId,
    Name,
    Validity,
    PubKeyInfo,
    UID,
    Extensions,
>> for TBSCertificateFrom<
    Serial,
    AlgoId,
    Name,
    Validity,
    PubKeyInfo,
    UID,
    Extensions,
> {
    closed spec fn spec_from(s: TBSCertificatePoly<
        Serial,
        AlgoId,
        Name,
        Validity,
        PubKeyInfo,
        UID,
        Extensions,
    >) -> Self {
        PairValue(s.version,
        PairValue(s.serial,
        PairValue(s.signature,
        PairValue(s.issuer,
        PairValue(s.validity,
        PairValue(s.subject,
        PairValue(s.subject_key,
        PairValue(s.issuer_uid,
        PairValue(s.subject_uid,
        PairValue(s.extensions,
        EndValue,
        ))))))))))
    }
}

impl<
    Serial,
    AlgoId,
    Name,
    Validity,
    PubKeyInfo,
    UID,
    Extensions,
> SpecFrom<TBSCertificateFrom<
    Serial,
    AlgoId,
    Name,
    Validity,
    PubKeyInfo,
    UID,
    Extensions,
>> for TBSCertificatePoly<
    Serial,
    AlgoId,
    Name,
    Validity,
    PubKeyInfo,
    UID,
    Extensions,
> {
    closed spec fn spec_from(s: TBSCertificateFrom<
        Serial,
        AlgoId,
        Name,
        Validity,
        PubKeyInfo,
        UID,
        Extensions,
    >) -> Self {
        TBSCertificatePoly {
            version: s.0,
            serial: s.1.0,
            signature: s.1.1.0,
            issuer: s.1.1.1.0,
            validity: s.1.1.1.1.0,
            subject: s.1.1.1.1.1.0,
            subject_key: s.1.1.1.1.1.1.0,
            issuer_uid: s.1.1.1.1.1.1.1.0,
            subject_uid: s.1.1.1.1.1.1.1.1.0,
            extensions: s.1.1.1.1.1.1.1.1.1.0,
        }
    }
}

impl<
    Serial: View,
    AlgoId: View,
    Name: View,
    Validity: View,
    PubKeyInfo: View,
    UID: View,
    Extensions: View,
> From<TBSCertificatePoly<
    Serial,
    AlgoId,
    Name,
    Validity,
    PubKeyInfo,
    UID,
    Extensions,
>> for TBSCertificateFrom<
    Serial,
    AlgoId,
    Name,
    Validity,
    PubKeyInfo,
    UID,
    Extensions,
> {
    fn ex_from(s: TBSCertificatePoly<
        Serial,
        AlgoId,
        Name,
        Validity,
        PubKeyInfo,
        UID,
        Extensions,
    >) -> Self {
        PairValue(s.version,
        PairValue(s.serial,
        PairValue(s.signature,
        PairValue(s.issuer,
        PairValue(s.validity,
        PairValue(s.subject,
        PairValue(s.subject_key,
        PairValue(s.issuer_uid,
        PairValue(s.subject_uid,
        PairValue(s.extensions,
        EndValue,
        ))))))))))
    }
}

impl<
    Serial: View,
    AlgoId: View,
    Name: View,
    Validity: View,
    PubKeyInfo: View,
    UID: View,
    Extensions: View,
> From<TBSCertificateFrom<
    Serial,
    AlgoId,
    Name,
    Validity,
    PubKeyInfo,
    UID,
    Extensions,
>> for TBSCertificatePoly<
    Serial,
    AlgoId,
    Name,
    Validity,
    PubKeyInfo,
    UID,
    Extensions,
> {
    fn ex_from(s: TBSCertificateFrom<
        Serial,
        AlgoId,
        Name,
        Validity,
        PubKeyInfo,
        UID,
        Extensions,
    >) -> Self {
        TBSCertificatePoly {
            version: s.0,
            serial: s.1.0,
            signature: s.1.1.0,
            issuer: s.1.1.1.0,
            validity: s.1.1.1.1.0,
            subject: s.1.1.1.1.1.0,
            subject_key: s.1.1.1.1.1.1.0,
            issuer_uid: s.1.1.1.1.1.1.1.0,
            subject_uid: s.1.1.1.1.1.1.1.1.0,
            extensions: s.1.1.1.1.1.1.1.1.1.0,
        }
    }
}

#[derive(Debug, View)]
pub struct TBSCertificateMapper;

impl SpecIso for TBSCertificateMapper {
    type Src = TBSCertificateFrom<
            SpecBigIntValue,
            SpecAlgorithmIdentifierValue,
            SpecNameValue,
            SpecValidityValue,
            SpecPublicKeyInfoValue,
            SpecBitStringValue,
            Seq<SpecExtensionValue>,
        >;
    type Dst = SpecTBSCertificateValue;

    proof fn spec_iso(s: Self::Src) {
        assert(s.1.1.1.1.1.1.1.1.1.1 == EndValue);
    }
    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl Iso for TBSCertificateMapper {
    type Src<'a> = TBSCertificateFrom<
            BigIntValue<'a>,
            AlgorithmIdentifierValue<'a>,
            NameValue<'a>,
            ValidityValue<'a>,
            PublicKeyInfoValue<'a>,
            BitStringValue<'a>,
            VecDeep<ExtensionValue<'a>>,
        >;
    type Dst<'a> = TBSCertificateValue<'a>;

    type SrcOwned = TBSCertificateFrom<
            BigIntOwned,
            AlgorithmIdentifierValueOwned,
            NameValueOwned,
            ValidityValueOwned,
            PublicKeyInfoValueOwned,
            BitStringValueOwned,
            VecDeep<ExtensionValueOwned>,
        >;
    type DstOwned = TBSCertificateValueOwned;
}

}
