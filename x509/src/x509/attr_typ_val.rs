use vstd::prelude::*;

use crate::asn1::*;
use crate::common::*;

use super::dir_string::*;
use crate::common::SpecFrom;

verus! {

/// AttributeTypeAndValue in X.509:
/// AttributeTypeAndValue ::= SEQUENCE {
///     type     AttributeType,
///     value    AttributeValue
/// }
///
/// AttributeType ::= OBJECT IDENTIFIER
/// AttributeValue ::= ANY DEFINED BY AttributeType
///
/// where "in general AttributeValue will be a DirectoryString" (4.1.2.4, RFC 2459)
pub type AttributeTypeAndValueInner = Mapped<LengthWrapped<(ASN1<ObjectIdentifier>, DirectoryString)>, AttributeTypeAndValueMapper>;

wrap_combinator! {
    struct AttributeTypeAndValue: AttributeTypeAndValueInner =>
        spec SpecAttributeTypeAndValueValue,
        exec<'a> AttributeTypeAndValueValue<'a>,
        owned AttributeTypeAndValueValueOwned,
    = Mapped {
            inner: LengthWrapped((ASN1(ObjectIdentifier), DirectoryString)),
            mapper: AttributeTypeAndValueMapper,
        };
}

asn1_tagged!(AttributeTypeAndValue, TagValue {
    class: TagClass::Universal,
    form: TagForm::Constructed,
    num: 0x10,
});

mapper! {
    pub struct AttributeTypeAndValueMapper;

    for <Typ, Value>
    from AttributeTypeAndValueFrom where type AttributeTypeAndValueFrom<Typ, Value> = (Typ, Value);
    to AttributeTypeAndValuePoly where pub struct AttributeTypeAndValuePoly<Typ, Value> {
        pub typ: Typ,
        pub value: Value,
    }

    spec SpecAttributeTypeAndValueValue with <SpecObjectIdentifierValue, SpecDirectoryStringValue>;
    exec AttributeTypeAndValueValue<'a> with <ObjectIdentifierValue, DirectoryStringValue<'a>>;
    owned AttributeTypeAndValueValueOwned with <ObjectIdentifierValueOwned, DirectoryStringValueOwned>;

    forward(x) {
        AttributeTypeAndValuePoly {
            typ: x.0,
            value: x.1,
        }
    }

    backward(y) {
        (y.typ, y.value)
    }
}

}

#[cfg(test)]
mod test {
    use super::*;

    verus! {
        /// Check that all trait bounds and preconditions are satisfied
        #[test]
        fn is_combinator() {
            let _ = ASN1(AttributeTypeAndValue).parse(&[]);
        }
    }

    #[test]
    fn sanity() {
        assert!(ASN1(AttributeTypeAndValue).parse(&[
            0x30, 0x17, 0x06, 0x0A, 0x09, 0x92, 0x26, 0x89, 0x93, 0xF2, 0x2C, 0x64, 0x01, 0x19, 0x16, 0x09, 0x72, 0x75, 0x62, 0x79, 0x2D, 0x6C, 0x61, 0x6E, 0x67,
        ]).is_ok());
    }
}
