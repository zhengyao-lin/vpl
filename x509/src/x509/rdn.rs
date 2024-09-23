use vstd::prelude::*;

use crate::asn1::*;
use crate::common::*;

use super::attr_typ_val::*;

verus! {

/// In X.509: RelativeDistinguishedName ::= SET OF AttributeTypeAndValue
/// TODO: support SET OF instead of using a sequence
pub type RDNInner = Mapped<SequenceOf<ASN1<AttributeTypeAndValue>>, RDNMapper>;

wrap_combinator! {
    struct RDN: RDNInner =>
        spec SpecRDNValue,
        exec<'a> RDNValue<'a>,
        owned RDNValueOwned,
    =
        Mapped {
            inner: SequenceOf(ASN1(AttributeTypeAndValue)),
            mapper: RDNMapper,
        };
}

// Override the tag to SET OF
asn1_tagged!(RDN, TagValue {
    class: TagClass::Universal,
    form: TagForm::Constructed,
    num: 0x11,
});

#[derive(Debug, View, PolyfillClone)]
pub struct RDNPoly<Attrs> {
    pub attrs: Attrs,
}

pub type SpecRDNValue = RDNPoly<Seq<SpecAttributeTypeAndValueValue>>;
pub type RDNValue<'a> = RDNPoly<VecDeep<AttributeTypeAndValueValue<'a>>>;
pub type RDNValueOwned = RDNPoly<VecDeep<AttributeTypeAndValueValueOwned>>;

type RDNFrom<T> = T;

impl<T> SpecFrom<RDNPoly<Seq<T>>> for RDNFrom<Seq<T>> {
    closed spec fn spec_from(s: RDNPoly<Seq<T>>) -> Self {
        s.attrs
    }
}

impl<T> SpecFrom<RDNFrom<T>> for RDNPoly<T> {
    closed spec fn spec_from(s: RDNFrom<T>) -> Self {
        RDNPoly {
            attrs: s,
        }
    }
}

impl<T: View> From<RDNPoly<VecDeep<T>>> for RDNFrom<VecDeep<T>> {
    fn ex_from(s: RDNPoly<VecDeep<T>>) -> Self {
        s.attrs
    }
}

impl<T: View> From<RDNFrom<T>> for RDNPoly<T> {
    fn ex_from(s: RDNFrom<T>) -> Self {
        RDNPoly {
            attrs: s,
        }
    }
}

#[derive(Debug, View)]
pub struct RDNMapper;

impl SpecIso for RDNMapper {
    type Src = RDNFrom<Seq<SpecAttributeTypeAndValueValue>>;
    type Dst = RDNPoly<Seq<SpecAttributeTypeAndValueValue>>;

    proof fn spec_iso(s: Self::Src) {}
    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl Iso for RDNMapper {
    type Src<'a> = RDNFrom<VecDeep<AttributeTypeAndValueValue<'a>>>;
    type Dst<'a> = RDNPoly<VecDeep<AttributeTypeAndValueValue<'a>>>;

    type SrcOwned = RDNFrom<VecDeep<AttributeTypeAndValueValueOwned>>;
    type DstOwned = RDNPoly<VecDeep<AttributeTypeAndValueValueOwned>>;
}

}

#[cfg(test)]
mod test {
    use super::*;

    verus! {
        /// Check that all trait bounds and preconditions are satisfied
        #[test]
        fn is_combinator() {
            let _ = ASN1(RDN).parse(&[]);
        }
    }

    #[test]
    fn sanity() {
        assert!(ASN1(RDN).parse(&[
            0x31, 0x0B, 0x30, 0x09, 0x06, 0x03, 0x55, 0x04, 0x06, 0x13, 0x02, 0x50, 0x41,
        ]).is_ok());
    }
}
