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

#[derive(Debug)]
pub struct NamePoly<RDNS> {
    pub rdns: RDNS,
}

pub type SpecNameValue = NamePoly<Seq<SpecRDNValue>>;
pub type NameValue<'a> = NamePoly<Vec<RDNValue<'a>>>;
pub type NameOwned = NamePoly<Vec<RDNOwned>>;

// type SpecNameInner = Seq<SpecRDNValue>;
// type NameInner<T> = RepeatValue<T>;

type NameFrom<T> = T;

impl<T: View> View for NamePoly<Vec<T>> {
    type V = NamePoly<Seq<T::V>>;

    closed spec fn view(&self) -> Self::V {
        NamePoly {
            rdns: Seq::new(self.rdns.len() as nat, |i| self.rdns@[i]@),
        }
    }
}

impl<T: PolyfillClone> PolyfillClone for NamePoly<Vec<T>> {
    fn clone(&self) -> Self {
        NamePoly {
            rdns: clone_vec_inner(&self.rdns),
        }
    }
}

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

impl<T: View> From<NamePoly<Vec<T>>> for NameFrom<VecDeep<T>> {
    fn ex_from(s: NamePoly<Vec<T>>) -> Self {
        VecDeep::from_vec(s.rdns)
    }
}

impl<T: View> From<NameFrom<VecDeep<T>>> for NamePoly<Vec<T>> {
    fn ex_from(s: NameFrom<VecDeep<T>>) -> Self {
        NamePoly {
            rdns: s.to_vec(),
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
    type Dst<'a> = NamePoly<Vec<RDNValue<'a>>>;

    type SrcOwned = NameFrom<VecDeep<RDNOwned>>;
    type DstOwned = NamePoly<Vec<RDNOwned>>;
}

}
