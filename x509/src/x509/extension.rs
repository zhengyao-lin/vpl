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
pub type Extension = Mapped<ASN1<ExplicitTag<(
    ASN1<ObjectIdentifier>,
    Optional<ASN1<Boolean>, ASN1<OctetString>>,
)>>, ExtensionMapper>;

pub fn extension() -> Extension {
    Mapped {
        inner: ASN1(ExplicitTag(TagValue {
            class: TagClass::Universal,
            form: TagForm::Constructed,
            num: 0x10,
        }, (
            ASN1(ObjectIdentifier),
            Optional::new(
                ASN1(Boolean),
                ASN1(OctetString),
            ),
        ))),
        mapper: ExtensionMapper,
    }
}

#[derive(Debug, View, PolyfillClone)]
pub struct ExtensionPoly<Id, Value> {
    pub id: Id,
    pub critical: OptionDeep<bool>,
    pub value: Value,
}

pub type SpecExtensionValue = ExtensionPoly<SpecObjectIdentifierValue, Seq<u8>>;
pub type ExtensionValue<'a> = ExtensionPoly<ObjectIdentifierValue, &'a [u8]>;
pub type ExtensionOwned = ExtensionPoly<ObjectIdentifierValueOwned, Vec<u8>>;

type ExtensionFrom<Id, Value> = (Id, (OptionDeep<bool>, Value));

impl<Id, Value> SpecFrom<ExtensionPoly<Id, Value>> for ExtensionFrom<Id, Value> {
    closed spec fn spec_from(s: ExtensionPoly<Id, Value>) -> Self {
        (s.id, (s.critical, s.value))
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
        (s.id, (s.critical, s.value))
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
