use vstd::prelude::*;

use crate::asn1::*;
use crate::common::*;

use super::rdn::*;

verus! {

/// In X.509: Name ::= SEQUENCE OF RelativeDistinguishedName
pub type Name = Mapped<ASN1<SequenceOf<RDN>>, NameMapper>;

pub fn name() -> Name {
    Mapped {
        inner: ASN1(SequenceOf(rdn())),
        mapper: NameMapper,
    }
}

#[derive(Debug, View, PolyfillClone)]
pub struct NamePoly<RDNS> {
    pub rdns: RDNS,
}

pub type SpecNameValue = NamePoly<Seq<SpecRDNValue>>;
pub type NameValue<'a> = NamePoly<VecDeep<RDNValue<'a>>>;
pub type NameOwned = NamePoly<VecDeep<RDNOwned>>;

type NameFrom<T> = T;

impl<T> SpecFrom<NamePoly<Seq<T>>> for NameFrom<Seq<T>> {
    closed spec fn spec_from(s: NamePoly<Seq<T>>) -> Self {
        s.rdns
    }
}

impl<T> SpecFrom<NameFrom<T>> for NamePoly<T> {
    closed spec fn spec_from(s: NameFrom<T>) -> Self {
        NamePoly {
            rdns: s,
        }
    }
}

impl<T: View> From<NamePoly<VecDeep<T>>> for NameFrom<VecDeep<T>> {
    fn ex_from(s: NamePoly<VecDeep<T>>) -> Self {
        s.rdns
    }
}

impl<T: View> From<NameFrom<T>> for NamePoly<T> {
    fn ex_from(s: NameFrom<T>) -> Self {
        NamePoly {
            rdns: s,
        }
    }
}

#[derive(Debug, View)]
pub struct NameMapper;

impl SpecIso for NameMapper {
    type Src = NameFrom<Seq<SpecRDNValue>>;
    type Dst = NamePoly<Seq<SpecRDNValue>>;

    proof fn spec_iso(s: Self::Src) {}
    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl Iso for NameMapper {
    type Src<'a> = NameFrom<VecDeep<RDNValue<'a>>>;
    type Dst<'a> = NamePoly<VecDeep<RDNValue<'a>>>;

    type SrcOwned = NameFrom<VecDeep<RDNOwned>>;
    type DstOwned = NamePoly<VecDeep<RDNOwned>>;
}

}
