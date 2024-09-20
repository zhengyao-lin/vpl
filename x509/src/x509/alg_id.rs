use vstd::prelude::*;

use crate::asn1::*;
use crate::common::*;

verus! {

/// In X.509:
/// AlgorithmIdentifier  ::=  SEQUENCE  {
///     algorithm               OBJECT IDENTIFIER,
///     parameters              ANY DEFINED BY algorithm OPTIONAL
/// }
///
/// TODO: right now parameters are parsed as a byte sequence
pub type AlgorithmIdentifierInner = Mapped<LengthWrapped<(ASN1<ObjectIdentifier>, Tail)>, AlgorithmIdentifierMapper>;

wrap_combinator! {
    struct AlgorithmIdentifier: AlgorithmIdentifierInner =>
        SpecAlgorithmIdentifierValue,
        AlgorithmIdentifierValue<'a>,
        AlgorithmIdentifierOwned
    = Mapped {
            inner: LengthWrapped((ASN1(ObjectIdentifier), Tail)),
            mapper: AlgorithmIdentifierMapper,
        };
}

asn1_tagged!(AlgorithmIdentifier, TagValue {
    class: TagClass::Universal,
    form: TagForm::Constructed,
    num: 0x10,
});

#[derive(Debug, View, PolyfillClone)]
pub struct AlgorithmIdentifierTo<Alg, Params> {
    pub alg: Alg,
    pub params: Params,
}

type AlgorithmIdentifierFrom<Alg, Params> = (Alg, Params);

pub type SpecAlgorithmIdentifierValue = AlgorithmIdentifierTo<SpecObjectIdentifierValue, Seq<u8>>;
pub type AlgorithmIdentifierValue<'a> = AlgorithmIdentifierTo<ObjectIdentifierValue, &'a [u8]>;
pub type AlgorithmIdentifierOwned = AlgorithmIdentifierTo<ObjectIdentifierValueOwned, Vec<u8>>;

impl<Alg, Params> SpecFrom<AlgorithmIdentifierTo<Alg, Params>> for AlgorithmIdentifierFrom<Alg, Params> {
    closed spec fn spec_from(s: AlgorithmIdentifierTo<Alg, Params>) -> Self {
        (s.alg, s.params)
    }
}

impl<Alg, Params> SpecFrom<AlgorithmIdentifierFrom<Alg, Params>> for AlgorithmIdentifierTo<Alg, Params> {
    closed spec fn spec_from(s: AlgorithmIdentifierFrom<Alg, Params>) -> Self {
        AlgorithmIdentifierTo {
            alg: s.0,
            params: s.1,
        }
    }
}

impl<Alg: View, Params: View> From<AlgorithmIdentifierTo<Alg, Params>> for AlgorithmIdentifierFrom<Alg, Params> where
{
    fn ex_from(s: AlgorithmIdentifierTo<Alg, Params>) -> Self {
        (s.alg, s.params)
    }
}

impl<Alg: View, Params: View> From<AlgorithmIdentifierFrom<Alg, Params>> for AlgorithmIdentifierTo<Alg, Params> {
    fn ex_from(s: AlgorithmIdentifierFrom<Alg, Params>) -> Self {
        AlgorithmIdentifierTo {
            alg: s.0,
            params: s.1,
        }
    }
}

#[derive(Debug, View)]
pub struct AlgorithmIdentifierMapper;

impl SpecIso for AlgorithmIdentifierMapper {
    type Src = AlgorithmIdentifierFrom<SpecObjectIdentifierValue, Seq<u8>>;
    type Dst = AlgorithmIdentifierTo<SpecObjectIdentifierValue, Seq<u8>>;

    proof fn spec_iso(s: Self::Src) {}
    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl Iso for AlgorithmIdentifierMapper {
    type Src<'a> = AlgorithmIdentifierFrom<ObjectIdentifierValue, &'a [u8]>;
    type Dst<'a> = AlgorithmIdentifierTo<ObjectIdentifierValue, &'a [u8]>;

    type SrcOwned = AlgorithmIdentifierFrom<ObjectIdentifierValueOwned, Vec<u8>>;
    type DstOwned = AlgorithmIdentifierTo<ObjectIdentifierValueOwned, Vec<u8>>;
}

}
