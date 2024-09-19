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
    OrdChoice<
        (ASN1<Boolean>, ASN1<OctetString>),
        ASN1<OctetString>,
    >,
)>>, ExtensionMapper>;

pub fn extension() -> Extension {
    Mapped {
        inner: ASN1(ExplicitTag(TagValue {
            class: TagClass::Universal,
            form: TagForm::Constructed,
            num: 0x10,
        }, (
            ASN1(ObjectIdentifier),
            OrdChoice::new(
                (ASN1(Boolean), ASN1(OctetString)),
                ASN1(OctetString),
            ),
        ))),
        mapper: ExtensionMapper,
    }
}

#[derive(Debug)]
pub struct ExtensionPoly<Id, Value> {
    pub id: Id,
    pub critical: Option<bool>,
    pub value: Value,
}

pub type SpecExtensionValue = ExtensionPoly<SpecObjectIdentifierValue, Seq<u8>>;
pub type ExtensionValue<'a> = ExtensionPoly<ObjectIdentifierValue, &'a [u8]>;
pub type ExtensionOwned = ExtensionPoly<ObjectIdentifierValueOwned, Vec<u8>>;

type ExtensionFrom<Id, Value> = (Id, Either<(bool, Value), Value>);

impl<Id: View, Value: View> View for ExtensionPoly<Id, Value> {
    type V = ExtensionPoly<Id::V, Value::V>;

    closed spec fn view(&self) -> Self::V {
        ExtensionPoly {
            id: self.id@,
            critical: self.critical,
            value: self.value@,
        }
    }
}

impl<Id: PolyfillClone, Value: PolyfillClone> PolyfillClone for ExtensionPoly<Id, Value> {
    fn clone(&self) -> Self {
        ExtensionPoly {
            id: PolyfillClone::clone(&self.id),
            critical: match self.critical {
                Some(critical) => Some(critical),
                None => None,
            },
            value: PolyfillClone::clone(&self.value),
        }
    }
}

impl<Id, Value> SpecFrom<ExtensionPoly<Id, Value>> for ExtensionFrom<Id, Value> {
    closed spec fn spec_from(s: ExtensionPoly<Id, Value>) -> Self {
        (s.id, match s.critical {
            Some(critical) => Either::Left((critical, s.value)),
            None => Either::Right(s.value),
        })
    }
}

impl<Id, Value> SpecFrom<ExtensionFrom<Id, Value>> for ExtensionPoly<Id, Value> {
    closed spec fn spec_from(s: ExtensionFrom<Id, Value>) -> Self {
        match s.1 {
            Either::Left((critical, value)) => ExtensionPoly {
                id: s.0,
                critical: Some(critical),
                value: value,
            },
            Either::Right(value) => ExtensionPoly {
                id: s.0,
                critical: None,
                value: value,
            },
        }
    }
}

impl<Id: View, Value: View> From<ExtensionPoly<Id, Value>> for ExtensionFrom<Id, Value> {
    fn ex_from(s: ExtensionPoly<Id, Value>) -> Self {
        (s.id, match s.critical {
            Some(critical) => Either::Left((critical, s.value)),
            None => Either::Right(s.value),
        })
    }
}

impl<Id: View, Value: View> From<ExtensionFrom<Id, Value>> for ExtensionPoly<Id, Value> {
    fn ex_from(s: ExtensionFrom<Id, Value>) -> Self {
        match s.1 {
            Either::Left((critical, value)) => ExtensionPoly {
                id: s.0,
                critical: Some(critical),
                value: value,
            },
            Either::Right(value) => ExtensionPoly {
                id: s.0,
                critical: None,
                value: value,
            },
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
