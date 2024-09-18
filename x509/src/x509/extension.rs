use vstd::prelude::*;

use crate::asn1::*;
use crate::asn1::Boolean;

use crate::common::*;
use crate::utils::*;

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

pub struct SpecExtensionValue {
    pub id: SpecObjectIdentifierValue,
    pub critical: Option<bool>,
    pub value: Seq<u8>,
}

#[derive(Debug)]
pub struct ExtensionValue<'a> {
    pub id: ObjectIdentifierValue,
    pub critical: Option<bool>,
    pub value: &'a [u8],
}

pub struct ExtensionOwned {
    pub id: ObjectIdentifierValueOwned,
    pub critical: Option<bool>,
    pub value: Vec<u8>,
}

type SpecExtensionInner = (SpecObjectIdentifierValue, Either<(bool, Seq<u8>), Seq<u8>>);
type ExtensionInner<'a> = (ObjectIdentifierValue, Either<(bool, &'a [u8]), &'a [u8]>);
type ExtensionInnerOwned = (ObjectIdentifierValueOwned, Either<(bool, Vec<u8>), Vec<u8>>);

impl<'a> PolyfillClone for ExtensionValue<'a> {
    fn clone(&self) -> Self {
        ExtensionValue {
            id: PolyfillClone::clone(&self.id),
            critical: match self.critical {
                Some(critical) => Some(critical),
                None => None,
            },
            value: PolyfillClone::clone(&self.value),
        }
    }
}

impl<'a> View for ExtensionValue<'a> {
    type V = SpecExtensionValue;

    closed spec fn view(&self) -> Self::V {
        SpecExtensionValue {
            id: self.id@,
            critical: self.critical,
            value: self.value@,
        }
    }
}

impl View for ExtensionOwned {
    type V = SpecExtensionValue;

    closed spec fn view(&self) -> Self::V {
        SpecExtensionValue {
            id: self.id@,
            critical: self.critical,
            value: self.value@,
        }
    }
}

impl SpecFrom<SpecExtensionValue> for SpecExtensionInner {
    closed spec fn spec_from(s: SpecExtensionValue) -> Self {
        (s.id, match s.critical {
            Some(critical) => Either::Left((critical, s.value)),
            None => Either::Right(s.value),
        })
    }
}

impl SpecFrom<SpecExtensionInner> for SpecExtensionValue {
    closed spec fn spec_from(s: SpecExtensionInner) -> Self {
        match s.1 {
            Either::Left((critical, value)) => SpecExtensionValue {
                id: s.0,
                critical: Some(critical),
                value: value,
            },
            Either::Right(value) => SpecExtensionValue {
                id: s.0,
                critical: None,
                value: value,
            },
        }
    }
}

impl<'a> From<ExtensionValue<'a>> for ExtensionInner<'a> {
    fn ex_from(s: ExtensionValue<'a>) -> Self {
        (s.id, match s.critical {
            Some(critical) => Either::Left((critical, s.value)),
            None => Either::Right(s.value),
        })
    }
}

impl<'a> From<ExtensionInner<'a>> for ExtensionValue<'a> {
    fn ex_from(s: ExtensionInner<'a>) -> Self {
        match s.1 {
            Either::Left((critical, value)) => ExtensionValue {
                id: s.0,
                critical: Some(critical),
                value: value,
            },
            Either::Right(value) => ExtensionValue {
                id: s.0,
                critical: None,
                value: value,
            },
        }
    }
}

impl From<ExtensionOwned> for ExtensionInnerOwned {
    fn ex_from(s: ExtensionOwned) -> Self {
        (s.id, match s.critical {
            Some(critical) => Either::Left((critical, s.value)),
            None => Either::Right(s.value),
        })
    }
}

impl From<ExtensionInnerOwned> for ExtensionOwned {
    fn ex_from(s: ExtensionInnerOwned) -> Self {
        match s.1 {
            Either::Left((critical, value)) => ExtensionOwned {
                id: s.0,
                critical: Some(critical),
                value: value,
            },
            Either::Right(value) => ExtensionOwned {
                id: s.0,
                critical: None,
                value: value,
            },
        }
    }
}

pub struct ExtensionMapper;
impl_trivial_view!(ExtensionMapper);
impl_trivial_poly_clone!(ExtensionMapper);

impl SpecIso for ExtensionMapper {
    type Src = SpecExtensionInner;
    type Dst = SpecExtensionValue;

    proof fn spec_iso(s: Self::Src) {}
    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl Iso for ExtensionMapper {
    type Src<'a> = ExtensionInner<'a>;
    type Dst<'a> = ExtensionValue<'a>;

    type SrcOwned = ExtensionInnerOwned;
    type DstOwned = ExtensionOwned;
}

}
