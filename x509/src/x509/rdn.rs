use vstd::prelude::*;

use crate::asn1::*;
use crate::common::*;

use super::attr_typ_val::*;

verus! {

/// In X.509: RelativeDistinguishedName ::= SET OF AttributeTypeAndValue
/// TODO: support SET OF instead of using a sequence
pub type RDNInner = SequenceOf<ASN1<AttributeTypeAndValue>>;

wrap_combinator! {
    pub struct RDN: RDNInner =>
        spec SpecRDNValue,
        exec<'a> RDNValue<'a>,
        owned RDNValueOwned,
    = SequenceOf(ASN1(AttributeTypeAndValue));
}

// Override the tag to SET OF
asn1_tagged!(RDN, TagValue {
    class: TagClass::Universal,
    form: TagForm::Constructed,
    num: 0x11,
});

pub type SpecRDNValue = Seq<SpecAttributeTypeAndValueValue>;
pub type RDNValue<'a> = VecDeep<AttributeTypeAndValueValue<'a>>;
pub type RDNValueOwned = VecDeep<AttributeTypeAndValueValueOwned>;

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
