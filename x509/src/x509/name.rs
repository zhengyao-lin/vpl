use vstd::prelude::*;

use crate::asn1::*;
use crate::common::*;
use crate::utils::*;

use super::rdn::*;

verus! {

/// In X.509: Name ::= SEQUENCE OF RelativeDistinguishedName
pub type NameCombinator = Mapped<ASN1<SequenceOf<RelativeDistinguishedNameCombinator>>, NameMapper>;

pub fn x509_name() -> NameCombinator {
    Mapped {
        inner: ASN1(SequenceOf(x509_relative_distinguished_name())),
        mapper: NameMapper,
    }
}

type SpecNameInner = Seq<SpecRelativeDistinguishedName>;
type NameInner<'a> = RepeatResult<RelativeDistinguishedName<'a>>;
type NameInnerOwned = RepeatResultOwned<RelativeDistinguishedNameOwned>;

pub struct SpecName {
    rdns: Seq<SpecRelativeDistinguishedName>,
}

#[derive(Debug)]
pub struct Name<'a> {
    rdns: Vec<RelativeDistinguishedName<'a>>,
}

pub struct NameOwned {
    rdns: Vec<RelativeDistinguishedNameOwned>,
}

impl<'a> View for Name<'a> {
    type V = SpecName;

    closed spec fn view(&self) -> Self::V {
        SpecName {
            rdns: Seq::new(self.rdns.len() as nat, |i| self.rdns@[i]@),
        }
    }
}

impl View for NameOwned {
    type V = SpecName;

    closed spec fn view(&self) -> Self::V {
        SpecName {
            rdns: Seq::new(self.rdns.len() as nat, |i| self.rdns@[i]@),
        }
    }
}

impl<'a> PolyfillClone for Name<'a> {
    fn clone(&self) -> Self {
        Name {
            rdns: clone_vec_inner(&self.rdns),
        }
    }
}

impl SpecFrom<SpecName> for SpecNameInner {
    closed spec fn spec_from(s: SpecName) -> Self {
        s.rdns
    }
}

impl SpecFrom<SpecNameInner> for SpecName {
    closed spec fn spec_from(s: SpecNameInner) -> Self {
        SpecName {
            rdns: s,
        }
    }
}

impl<'a> From<Name<'a>> for NameInner<'a> {
    fn ex_from(s: Name<'a>) -> Self {
        RepeatResult(s.rdns)
    }
}

impl<'a> From<NameInner<'a>> for Name<'a> {
    fn ex_from(s: NameInner<'a>) -> Self {
        Name {
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

#[derive(Debug)]
pub struct NameMapper;
impl_trivial_view!(NameMapper);
impl_trivial_poly_clone!(NameMapper);

impl SpecIso for NameMapper {
    type Src = SpecNameInner;
    type Dst = SpecName;

    proof fn spec_iso(s: Self::Src) {}
    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl Iso for NameMapper {
    type Src<'a> = NameInner<'a>;
    type Dst<'a> = Name<'a>;

    type SrcOwned = NameInnerOwned;
    type DstOwned = NameOwned;
}

}
