use vstd::prelude::*;

use crate::asn1::*;
use crate::asn1::Boolean;

use crate::common::*;

verus! {

/// Extension  ::=  SEQUENCE  {
///     extnID      OBJECT IDENTIFIER,
///     critical    BOOLEAN DEFAULT FALSE,
///     extnValue   OCTET STRING
/// }
pub type ExtensionInner = Mapped<LengthWrapped<Pair<
    ASN1<ObjectIdentifier>,
    Optional<ASN1<Boolean>, ASN1<OctetString>>,
>>, ExtensionMapper>;

pub type ExtensionsInner = SequenceOf<ASN1<Extension>>;

wrap_combinator! {
    struct Extension: ExtensionInner =>
        spec SpecExtensionValue,
        exec<'a> ExtensionValue<'a>,
        owned ExtensionValueOwned,
    = Mapped {
            inner: LengthWrapped(Pair(
                ASN1(ObjectIdentifier),
                Optional(
                    ASN1(Boolean),
                    ASN1(OctetString),
                ),
            )),
            mapper: ExtensionMapper,
        };
}

asn1_tagged!(Extension, TagValue {
    class: TagClass::Universal,
    form: TagForm::Constructed,
    num: 0x10,
});

wrap_combinator! {
    struct Extensions: ExtensionsInner = SequenceOf(ASN1(Extension));
}

asn1_tagged!(Extensions, TagValue {
    class: TagClass::Universal,
    form: TagForm::Constructed,
    num: 0x10,
});

#[derive(Debug, View, PolyfillClone)]
pub struct ExtensionPoly<Id, Value> {
    pub id: Id,
    pub critical: OptionDeep<bool>,
    pub value: Value,
}

pub type SpecExtensionValue = ExtensionPoly<SpecObjectIdentifierValue, Seq<u8>>;
pub type ExtensionValue<'a> = ExtensionPoly<ObjectIdentifierValue, &'a [u8]>;
pub type ExtensionValueOwned = ExtensionPoly<ObjectIdentifierValueOwned, Vec<u8>>;

type ExtensionFrom<Id, Value> = PairValue<Id, PairValue<OptionDeep<bool>, Value>>;

impl<Id, Value> SpecFrom<ExtensionPoly<Id, Value>> for ExtensionFrom<Id, Value> {
    closed spec fn spec_from(s: ExtensionPoly<Id, Value>) -> Self {
        PairValue(s.id, PairValue(s.critical, s.value))
    }
}

impl<Id, Value> SpecFrom<ExtensionFrom<Id, Value>> for ExtensionPoly<Id, Value> {
    closed spec fn spec_from(s: ExtensionFrom<Id, Value>) -> Self {
        ExtensionPoly {
            id: s.0,
            critical: s.1.0,
            value: s.1.1,
        }
    }
}

impl<Id: View, Value: View> From<ExtensionPoly<Id, Value>> for ExtensionFrom<Id, Value> {
    fn ex_from(s: ExtensionPoly<Id, Value>) -> Self {
        PairValue(s.id, PairValue(s.critical, s.value))
    }
}

impl<Id: View, Value: View> From<ExtensionFrom<Id, Value>> for ExtensionPoly<Id, Value> {
    fn ex_from(s: ExtensionFrom<Id, Value>) -> Self {
        ExtensionPoly {
            id: s.0,
            critical: s.1.0,
            value: s.1.1,
        }
    }
}

#[derive(Debug, View)]
pub struct ExtensionMapper;

impl SpecIso for ExtensionMapper {
    type Src = ExtensionFrom<SpecObjectIdentifierValue, Seq<u8>>;
    type Dst = ExtensionPoly<SpecObjectIdentifierValue, Seq<u8>>;

    proof fn spec_iso(s: Self::Src) {}
    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl Iso for ExtensionMapper {
    type Src<'a> = ExtensionFrom<ObjectIdentifierValue, &'a [u8]>;
    type Dst<'a> = ExtensionPoly<ObjectIdentifierValue, &'a [u8]>;

    type SrcOwned = ExtensionFrom<ObjectIdentifierValueOwned, Vec<u8>>;
    type DstOwned = ExtensionPoly<ObjectIdentifierValueOwned, Vec<u8>>;
}

}

#[cfg(test)]
mod test {
    use super::*;

    verus! {
        /// Check that all trait bounds and preconditions are satisfied
        #[test]
        fn is_combinator() {
            let _ = ASN1(Extension).parse(&[]);
            let _ = ASN1(Extensions).parse(&[]);
        }
    }

    #[test]
    fn sanity() {
        assert!(ASN1(Extension).parse(&[
            0x30, 0x1D, 0x06, 0x03, 0x55, 0x1D, 0x0E, 0x04, 0x16, 0x04, 0x14, 0xE4, 0xAF, 0x2B, 0x26, 0x71, 0x1A, 0x2B, 0x48, 0x27, 0x85, 0x2F, 0x52, 0x66, 0x2C, 0xEF, 0xF0, 0x89, 0x13, 0x71, 0x3E,
        ]).is_ok());

        assert!(ASN1(Extensions).parse(&[
            0x30, 0x40, 0x30, 0x0E, 0x06, 0x03, 0x55, 0x1D, 0x0F, 0x01, 0x01, 0xFF, 0x04, 0x04, 0x03, 0x02, 0x01, 0x86, 0x30, 0x0F, 0x06, 0x03, 0x55, 0x1D, 0x13, 0x01, 0x01, 0xFF, 0x04, 0x05, 0x30, 0x03, 0x01, 0x01, 0xFF, 0x30, 0x1D, 0x06, 0x03, 0x55, 0x1D, 0x0E, 0x04, 0x16, 0x04, 0x14, 0xE4, 0xAF, 0x2B, 0x26, 0x71, 0x1A, 0x2B, 0x48, 0x27, 0x85, 0x2F, 0x52, 0x66, 0x2C, 0xEF, 0xF0, 0x89, 0x13, 0x71, 0x3E,
        ]).is_ok());
    }
}
