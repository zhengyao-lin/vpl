use vstd::prelude::*;

use crate::asn1::*;
use crate::common::*;
use crate::utils::*;

verus! {

/// In X.509:
/// AlgorithmIdentifier  ::=  SEQUENCE  {
///     algorithm               OBJECT IDENTIFIER,
///     parameters              ANY DEFINED BY algorithm OPTIONAL
/// }
///
/// TODO: right now parameters are parsed as a byte sequence
pub type AlgorithmIdentifier = Mapped<ASN1<ExplicitTag<(ASN1<ObjectIdentifier>, Tail)>>, AlgorithmIdentifierMapper>;

pub fn algorithm_identifier() -> AlgorithmIdentifier {
    Mapped {
        inner: ASN1(ExplicitTag(TagValue {
            class: TagClass::Universal,
            form: TagForm::Constructed,
            num: 0x10,
        }, (ASN1(ObjectIdentifier), Tail))),
        mapper: AlgorithmIdentifierMapper,
    }
}

pub struct SpecAlgorithmIdentifierValue {
    pub alg: SpecObjectIdentifierValue,
    pub params: Seq<u8>,
}

#[derive(Debug)]
pub struct AlgorithmIdentifierValue<'a> {
    pub alg: ObjectIdentifierValue,
    pub params: &'a [u8],
}

pub struct AlgorithmIdentifierOwned {
    pub alg: ObjectIdentifierValueOwned,
    pub params: Vec<u8>,
}

type SpecAlgorithmIdentifierInner = (SpecObjectIdentifierValue, Seq<u8>);
type AlgorithmIdentifierInner<'a> = (ObjectIdentifierValue, &'a [u8]);
type AlgorithmIdentifierInnerOwned = (ObjectIdentifierValueOwned, Vec<u8>);

impl<'a> PolyfillClone for AlgorithmIdentifierValue<'a> {
    fn clone(&self) -> Self {
        AlgorithmIdentifierValue {
            alg: PolyfillClone::clone(&self.alg),
            params: PolyfillClone::clone(&self.params),
        }
    }
}

impl<'a> View for AlgorithmIdentifierValue<'a> {
    type V = SpecAlgorithmIdentifierValue;

    closed spec fn view(&self) -> Self::V {
        SpecAlgorithmIdentifierValue {
            alg: self.alg@,
            params: self.params@,
        }
    }
}

impl View for AlgorithmIdentifierOwned {
    type V = SpecAlgorithmIdentifierValue;

    closed spec fn view(&self) -> Self::V {
        SpecAlgorithmIdentifierValue {
            alg: self.alg@,
            params: self.params@,
        }
    }
}

impl SpecFrom<SpecAlgorithmIdentifierValue> for SpecAlgorithmIdentifierInner {
    closed spec fn spec_from(s: SpecAlgorithmIdentifierValue) -> Self {
        (s.alg, s.params)
    }
}

impl SpecFrom<SpecAlgorithmIdentifierInner> for SpecAlgorithmIdentifierValue {
    closed spec fn spec_from(s: SpecAlgorithmIdentifierInner) -> Self {
        SpecAlgorithmIdentifierValue {
            alg: s.0,
            params: s.1,
        }
    }
}

impl<'a> From<AlgorithmIdentifierValue<'a>> for AlgorithmIdentifierInner<'a> {
    fn ex_from(s: AlgorithmIdentifierValue<'a>) -> Self {
        (s.alg, s.params)
    }
}

impl<'a> From<AlgorithmIdentifierInner<'a>> for AlgorithmIdentifierValue<'a> {
    fn ex_from(s: AlgorithmIdentifierInner<'a>) -> Self {
        AlgorithmIdentifierValue {
            alg: s.0,
            params: s.1,
        }
    }
}

impl From<AlgorithmIdentifierOwned> for AlgorithmIdentifierInnerOwned {
    fn ex_from(s: AlgorithmIdentifierOwned) -> Self {
        (s.alg, s.params)
    }
}

impl From<AlgorithmIdentifierInnerOwned> for AlgorithmIdentifierOwned {
    fn ex_from(s: AlgorithmIdentifierInnerOwned) -> Self {
        AlgorithmIdentifierOwned {
            alg: s.0,
            params: s.1,
        }
    }
}

#[derive(Debug)]
pub struct AlgorithmIdentifierMapper;
impl_trivial_view!(AlgorithmIdentifierMapper);
impl_trivial_poly_clone!(AlgorithmIdentifierMapper);

impl SpecIso for AlgorithmIdentifierMapper {
    type Src = SpecAlgorithmIdentifierInner;
    type Dst = SpecAlgorithmIdentifierValue;

    proof fn spec_iso(s: Self::Src) {}
    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl Iso for AlgorithmIdentifierMapper {
    type Src<'a> = AlgorithmIdentifierInner<'a>;
    type Dst<'a> = AlgorithmIdentifierValue<'a>;

    type SrcOwned = AlgorithmIdentifierInnerOwned;
    type DstOwned = AlgorithmIdentifierOwned;
}

}
