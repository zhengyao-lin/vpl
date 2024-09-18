use vstd::prelude::*;

use crate::asn1::*;
use crate::common::*;
use crate::utils::*;

use super::alg_id::*;

verus! {

/// SubjectPublicKeyInfo  ::=  SEQUENCE  {
///     algorithm            AlgorithmIdentifier,
///     subjectPublicKey     BIT STRING
/// }
pub type PublicKeyInfoCombinator = Mapped<ASN1<ExplicitTag<(AlgorithmIdentifierCombinator, ASN1<BitString>)>>, PublicKeyInfoMapper>;

pub fn x509_public_key_info() -> PublicKeyInfoCombinator {
    Mapped {
        inner: ASN1(ExplicitTag(TagValue {
            class: TagClass::Universal,
            form: TagForm::Constructed,
            num: 0x10,
        }, (x509_algorithm_identifier(), ASN1(BitString)))),
        mapper: PublicKeyInfoMapper,
    }
}

pub struct SpecPublicKeyInfo {
    pub alg: SpecAlgorithmIdentifier,
    pub pub_key: SpecBitStringValue,
}

#[derive(Debug)]
pub struct PublicKeyInfo<'a> {
    pub alg: AlgorithmIdentifier<'a>,
    pub pub_key: BitStringValue<'a>,
}

pub struct PublicKeyInfoOwned {
    pub alg: AlgorithmIdentifierOwned,
    pub pub_key: BitStringValueOwned,
}

type SpecPublicKeyInfoInner = (SpecAlgorithmIdentifier, SpecBitStringValue);
type PublicKeyInfoInner<'a> = (AlgorithmIdentifier<'a>, BitStringValue<'a>);
type PublicKeyInfoInnerOwned = (AlgorithmIdentifierOwned, BitStringValueOwned);

impl<'a> PolyfillClone for PublicKeyInfo<'a> {
    fn clone(&self) -> Self {
        PublicKeyInfo {
            alg: PolyfillClone::clone(&self.alg),
            pub_key: PolyfillClone::clone(&self.pub_key),
        }
    }
}

impl<'a> View for PublicKeyInfo<'a> {
    type V = SpecPublicKeyInfo;

    closed spec fn view(&self) -> Self::V {
        SpecPublicKeyInfo {
            alg: self.alg@,
            pub_key: self.pub_key@,
        }
    }
}

impl View for PublicKeyInfoOwned {
    type V = SpecPublicKeyInfo;

    closed spec fn view(&self) -> Self::V {
        SpecPublicKeyInfo {
            alg: self.alg@,
            pub_key: self.pub_key@,
        }
    }
}

impl SpecFrom<SpecPublicKeyInfo> for SpecPublicKeyInfoInner {
    closed spec fn spec_from(s: SpecPublicKeyInfo) -> Self {
        (s.alg, s.pub_key)
    }
}

impl SpecFrom<SpecPublicKeyInfoInner> for SpecPublicKeyInfo {
    closed spec fn spec_from(s: SpecPublicKeyInfoInner) -> Self {
        SpecPublicKeyInfo {
            alg: s.0,
            pub_key: s.1,
        }
    }
}

impl<'a> From<PublicKeyInfo<'a>> for PublicKeyInfoInner<'a> {
    fn ex_from(s: PublicKeyInfo<'a>) -> Self {
        (s.alg, s.pub_key)
    }
}

impl<'a> From<PublicKeyInfoInner<'a>> for PublicKeyInfo<'a> {
    fn ex_from(s: PublicKeyInfoInner<'a>) -> Self {
        PublicKeyInfo {
            alg: s.0,
            pub_key: s.1,
        }
    }
}

impl From<PublicKeyInfoOwned> for PublicKeyInfoInnerOwned {
    fn ex_from(s: PublicKeyInfoOwned) -> Self {
        (s.alg, s.pub_key)
    }
}

impl From<PublicKeyInfoInnerOwned> for PublicKeyInfoOwned {
    fn ex_from(s: PublicKeyInfoInnerOwned) -> Self {
        PublicKeyInfoOwned {
            alg: s.0,
            pub_key: s.1,
        }
    }
}

#[derive(Debug)]
pub struct PublicKeyInfoMapper;
impl_trivial_view!(PublicKeyInfoMapper);
impl_trivial_poly_clone!(PublicKeyInfoMapper);

impl SpecIso for PublicKeyInfoMapper {
    type Src = SpecPublicKeyInfoInner;
    type Dst = SpecPublicKeyInfo;

    proof fn spec_iso(s: Self::Src) {}
    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl Iso for PublicKeyInfoMapper {
    type Src<'a> = PublicKeyInfoInner<'a>;
    type Dst<'a> = PublicKeyInfo<'a>;

    type SrcOwned = PublicKeyInfoInnerOwned;
    type DstOwned = PublicKeyInfoOwned;
}

}
