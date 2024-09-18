use vstd::prelude::*;

use crate::asn1::*;
use crate::asn1::vest::*;
use crate::asn1::Boolean;

use crate::utils::*;

verus! {

/// Extension  ::=  SEQUENCE  {
///     extnID      OBJECT IDENTIFIER,
///     critical    BOOLEAN DEFAULT FALSE,
///     extnValue   OCTET STRING
/// }
pub type ExtensionCombinator = Mapped<ASN1<ExplicitTag<(
    ASN1<ObjectIdentifier>,
    OrdChoice<
        (ASN1<Boolean>, ASN1<OctetString>),
        ASN1<OctetString>,
    >,
)>>, ExtensionMapper>;

pub fn x509_extension() -> ExtensionCombinator {
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

pub struct SpecExtension {
    pub id: SpecObjectIdentifierValue,
    pub critical: Option<bool>,
    pub value: Seq<u8>,
}

#[derive(Debug)]
pub struct Extension<'a> {
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

impl<'a> PolyfillClone for Extension<'a> {
    fn clone(&self) -> Self {
        Extension {
            id: PolyfillClone::clone(&self.id),
            critical: match self.critical {
                Some(critical) => Some(critical),
                None => None,
            },
            value: PolyfillClone::clone(&self.value),
        }
    }
}

impl<'a> View for Extension<'a> {
    type V = SpecExtension;

    closed spec fn view(&self) -> Self::V {
        SpecExtension {
            id: self.id@,
            critical: self.critical,
            value: self.value@,
        }
    }
}

impl View for ExtensionOwned {
    type V = SpecExtension;

    closed spec fn view(&self) -> Self::V {
        SpecExtension {
            id: self.id@,
            critical: self.critical,
            value: self.value@,
        }
    }
}

impl SpecFrom<SpecExtension> for SpecExtensionInner {
    closed spec fn spec_from(s: SpecExtension) -> Self {
        (s.id, match s.critical {
            Some(critical) => Either::Left((critical, s.value)),
            None => Either::Right(s.value),
        })
    }
}

impl SpecFrom<SpecExtensionInner> for SpecExtension {
    closed spec fn spec_from(s: SpecExtensionInner) -> Self {
        match s.1 {
            Either::Left((critical, value)) => SpecExtension {
                id: s.0,
                critical: Some(critical),
                value: value,
            },
            Either::Right(value) => SpecExtension {
                id: s.0,
                critical: None,
                value: value,
            },
        }
    }
}

impl<'a> From<Extension<'a>> for ExtensionInner<'a> {
    fn ex_from(s: Extension<'a>) -> Self {
        (s.id, match s.critical {
            Some(critical) => Either::Left((critical, s.value)),
            None => Either::Right(s.value),
        })
    }
}

impl<'a> From<ExtensionInner<'a>> for Extension<'a> {
    fn ex_from(s: ExtensionInner<'a>) -> Self {
        match s.1 {
            Either::Left((critical, value)) => Extension {
                id: s.0,
                critical: Some(critical),
                value: value,
            },
            Either::Right(value) => Extension {
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
    type Dst = SpecExtension;

    proof fn spec_iso(s: Self::Src) {}
    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl Iso for ExtensionMapper {
    type Src<'a> = ExtensionInner<'a>;
    type Dst<'a> = Extension<'a>;

    type SrcOwned = ExtensionInnerOwned;
    type DstOwned = ExtensionOwned;
}

}
