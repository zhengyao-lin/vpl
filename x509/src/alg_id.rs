use vstd::prelude::*;

use crate::asn1::*;
use crate::asn1::vest::*;

use crate::utils::*;

verus! {

/// In X.509:
/// AlgorithmIdentifier  ::=  SEQUENCE  {
///     algorithm               OBJECT IDENTIFIER,
///     parameters              ANY DEFINED BY algorithm OPTIONAL
/// }
///
/// TODO: right now parameters are parsed as a byte sequence
pub type AlgorithmIdentifierCombinator = Mapped<ASN1<ExplicitTag<(ASN1<ObjectIdentifier>, Tail)>>, AlgorithmIdentifierMapper>;

pub fn x509_algorithm_identifier() -> AlgorithmIdentifierCombinator {
    Mapped {
        inner: ASN1(ExplicitTag(TagValue {
            class: TagClass::Universal,
            form: TagForm::Constructed,
            num: 0x10,
        }, (ASN1(ObjectIdentifier), Tail))),
        mapper: AlgorithmIdentifierMapper,
    }
}

pub struct SpecAlgorithmIdentifier {
    pub alg: SpecObjectIdentifierValue,
    pub params: Seq<u8>,
}

#[derive(Debug)]
pub struct AlgorithmIdentifier<'a> {
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

impl<'a> PolyfillClone for AlgorithmIdentifier<'a> {
    fn clone(&self) -> Self {
        AlgorithmIdentifier {
            alg: PolyfillClone::clone(&self.alg),
            params: PolyfillClone::clone(&self.params),
        }
    }
}

impl<'a> View for AlgorithmIdentifier<'a> {
    type V = SpecAlgorithmIdentifier;

    closed spec fn view(&self) -> Self::V {
        SpecAlgorithmIdentifier {
            alg: self.alg@,
            params: self.params@,
        }
    }
}

impl View for AlgorithmIdentifierOwned {
    type V = SpecAlgorithmIdentifier;

    closed spec fn view(&self) -> Self::V {
        SpecAlgorithmIdentifier {
            alg: self.alg@,
            params: self.params@,
        }
    }
}

impl SpecFrom<SpecAlgorithmIdentifier> for SpecAlgorithmIdentifierInner {
    closed spec fn spec_from(s: SpecAlgorithmIdentifier) -> Self {
        (s.alg, s.params)
    }
}

impl SpecFrom<SpecAlgorithmIdentifierInner> for SpecAlgorithmIdentifier {
    closed spec fn spec_from(s: SpecAlgorithmIdentifierInner) -> Self {
        SpecAlgorithmIdentifier {
            alg: s.0,
            params: s.1,
        }
    }
}

impl<'a> From<AlgorithmIdentifier<'a>> for AlgorithmIdentifierInner<'a> {
    fn ex_from(s: AlgorithmIdentifier<'a>) -> Self {
        (s.alg, s.params)
    }
}

impl<'a> From<AlgorithmIdentifierInner<'a>> for AlgorithmIdentifier<'a> {
    fn ex_from(s: AlgorithmIdentifierInner<'a>) -> Self {
        AlgorithmIdentifier {
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
    type Dst = SpecAlgorithmIdentifier;

    proof fn spec_iso(s: Self::Src) {}
    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl Iso for AlgorithmIdentifierMapper {
    type Src<'a> = AlgorithmIdentifierInner<'a>;
    type Dst<'a> = AlgorithmIdentifier<'a>;

    type SrcOwned = AlgorithmIdentifierInnerOwned;
    type DstOwned = AlgorithmIdentifierOwned;
}

}
