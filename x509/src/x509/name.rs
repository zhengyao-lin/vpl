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

type SpecNameInner = Seq<SpecRDNValue>;
type NameInner<'a> = RepeatResult<RDNValue<'a>>;
type NameInnerOwned = RepeatResultOwned<RDNOwned>;

pub struct SpecNameValue {
    rdns: Seq<SpecRDNValue>,
}

#[derive(Debug)]
pub struct NameValue<'a> {
    rdns: Vec<RDNValue<'a>>,
}

pub struct NameOwned {
    rdns: Vec<RDNOwned>,
}

impl<'a> View for NameValue<'a> {
    type V = SpecNameValue;

    closed spec fn view(&self) -> Self::V {
        SpecNameValue {
            rdns: Seq::new(self.rdns.len() as nat, |i| self.rdns@[i]@),
        }
    }
}

impl View for NameOwned {
    type V = SpecNameValue;

    closed spec fn view(&self) -> Self::V {
        SpecNameValue {
            rdns: Seq::new(self.rdns.len() as nat, |i| self.rdns@[i]@),
        }
    }
}

impl<'a> PolyfillClone for NameValue<'a> {
    fn clone(&self) -> Self {
        NameValue {
            rdns: clone_vec_inner(&self.rdns),
        }
    }
}

impl SpecFrom<SpecNameValue> for SpecNameInner {
    closed spec fn spec_from(s: SpecNameValue) -> Self {
        s.rdns
    }
}

impl SpecFrom<SpecNameInner> for SpecNameValue {
    closed spec fn spec_from(s: SpecNameInner) -> Self {
        SpecNameValue {
            rdns: s,
        }
    }
}

impl<'a> From<NameValue<'a>> for NameInner<'a> {
    fn ex_from(s: NameValue<'a>) -> Self {
        RepeatResult(s.rdns)
    }
}

impl<'a> From<NameInner<'a>> for NameValue<'a> {
    fn ex_from(s: NameInner<'a>) -> Self {
        NameValue {
            rdns: s.0,
        }
    }
}

impl From<NameOwned> for NameInnerOwned {
    fn ex_from(s: NameOwned) -> Self {
        RepeatResultOwned(s.rdns)
    }
}

impl From<NameInnerOwned> for NameOwned {
    fn ex_from(s: NameInnerOwned) -> Self {
        NameOwned {
            rdns: s.0,
        }
    }
}

#[derive(Debug, View)]
pub struct NameMapper;

impl SpecIso for NameMapper {
    type Src = SpecNameInner;
    type Dst = SpecNameValue;

    proof fn spec_iso(s: Self::Src) {}
    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl Iso for NameMapper {
    type Src<'a> = NameInner<'a>;
    type Dst<'a> = NameValue<'a>;

    type SrcOwned = NameInnerOwned;
    type DstOwned = NameOwned;
}

}
