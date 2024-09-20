use vstd::prelude::*;

use crate::asn1::*;
use crate::common::*;

use super::alg_id::*;

verus! {

/// SubjectPublicKeyInfo  ::=  SEQUENCE  {
///     algorithm            AlgorithmIdentifier,
///     subjectPublicKey     BIT STRING
/// }
pub type PublicKeyInfoInner = Mapped<LengthWrapped<(ASN1<AlgorithmIdentifier>, ASN1<BitString>)>, PublicKeyInfoMapper>;

wrap_combinator! {
    struct PublicKeyInfo: PublicKeyInfoInner =>
        SpecPublicKeyInfoValue,
        PublicKeyInfoValue<'a>,
        PublicKeyInfoOwned
    =
        Mapped {
            inner: LengthWrapped((ASN1(AlgorithmIdentifier), ASN1(BitString))),
            mapper: PublicKeyInfoMapper,
        };
}

asn1_tagged!(PublicKeyInfo, TagValue {
    class: TagClass::Universal,
    form: TagForm::Constructed,
    num: 0x10,
});

#[derive(Debug, View, PolyfillClone)]
pub struct PublicKeyInfoPoly<Alg, PubKey> {
    pub alg: Alg,
    pub pub_key: PubKey,
}

pub type SpecPublicKeyInfoValue = PublicKeyInfoPoly<SpecAlgorithmIdentifierValue, SpecBitStringValue>;
pub type PublicKeyInfoValue<'a> = PublicKeyInfoPoly<AlgorithmIdentifierValue<'a>, BitStringValue<'a>>;
pub type PublicKeyInfoOwned = PublicKeyInfoPoly<AlgorithmIdentifierOwned, BitStringValueOwned>;

type PublicKeyInfoFrom<Alg, PubKey> = (Alg, PubKey);

impl<Alg, PubKey> SpecFrom<PublicKeyInfoPoly<Alg, PubKey>> for PublicKeyInfoFrom<Alg, PubKey> {
    closed spec fn spec_from(s: PublicKeyInfoPoly<Alg, PubKey>) -> Self {
        (s.alg, s.pub_key)
    }
}

impl<Alg, PubKey> SpecFrom<PublicKeyInfoFrom<Alg, PubKey>> for PublicKeyInfoPoly<Alg, PubKey> {
    closed spec fn spec_from(s: PublicKeyInfoFrom<Alg, PubKey>) -> Self {
        PublicKeyInfoPoly {
            alg: s.0,
            pub_key: s.1,
        }
    }
}

impl<Alg: View, PubKey: View> From<PublicKeyInfoPoly<Alg, PubKey>> for PublicKeyInfoFrom<Alg, PubKey> {
    fn ex_from(s: PublicKeyInfoPoly<Alg, PubKey>) -> Self {
        (s.alg, s.pub_key)
    }
}

impl<Alg: View, PubKey: View> From<PublicKeyInfoFrom<Alg, PubKey>> for PublicKeyInfoPoly<Alg, PubKey> {
    fn ex_from(s: PublicKeyInfoFrom<Alg, PubKey>) -> Self {
        PublicKeyInfoPoly {
            alg: s.0,
            pub_key: s.1,
        }
    }
}

#[derive(Debug, View)]
pub struct PublicKeyInfoMapper;

impl SpecIso for PublicKeyInfoMapper {
    type Src = PublicKeyInfoFrom<SpecAlgorithmIdentifierValue, SpecBitStringValue>;
    type Dst = PublicKeyInfoPoly<SpecAlgorithmIdentifierValue, SpecBitStringValue>;

    proof fn spec_iso(s: Self::Src) {}
    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl Iso for PublicKeyInfoMapper {
    type Src<'a> = PublicKeyInfoFrom<AlgorithmIdentifierValue<'a>, BitStringValue<'a>>;
    type Dst<'a> = PublicKeyInfoPoly<AlgorithmIdentifierValue<'a>, BitStringValue<'a>>;

    type SrcOwned = PublicKeyInfoFrom<AlgorithmIdentifierOwned, BitStringValueOwned>;
    type DstOwned = PublicKeyInfoPoly<AlgorithmIdentifierOwned, BitStringValueOwned>;
}

}
