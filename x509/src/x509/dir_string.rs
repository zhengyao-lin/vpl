use vstd::prelude::*;

use crate::asn1::*;
use crate::common::*;

verus! {

/// DirectoryString ::= CHOICE {
///     teletexString           TeletexString (SIZE (1..MAX)),
///     printableString         PrintableString (SIZE (1..MAX)),
///     universalString         UniversalString (SIZE (1..MAX)),
///     utf8String              UTF8String (SIZE (1.. MAX)), // More common
///     bmpString               BMPString (SIZE (1..MAX))
/// }
///
/// TODO: only supporting PrintableString and UTF8String for now
pub type DirectoryString = Mapped<OrdChoice<ASN1<PrintableString>, ASN1<UTF8String>>, DirectoryStringMapper>;

pub fn directory_string() -> DirectoryString {
    Mapped {
        inner: OrdChoice::new(
            ASN1(PrintableString),
            ASN1(UTF8String),
        ),
        mapper: DirectoryStringMapper,
    }
}

pub enum SpecDirectoryStringValue {
    PrintableString(SpecPrintableStringValue),
    UTF8String(SpecUTF8StringValue),
}

#[derive(Debug)]
pub enum DirectoryStringValue<'a> {
    PrintableString(PrintableStringValue<'a>),
    UTF8String(UTF8StringValue<'a>),
}

pub enum DirectoryStringOwned {
    PrintableString(PrintableStringValueOwned),
    UTF8String(UTF8StringValueOwned),
}

type SpecDirectoryStringInner = Either<SpecPrintableStringValue, SpecUTF8StringValue>;
type DirectoryStringInner<'a> = Either<PrintableStringValue<'a>, UTF8StringValue<'a>>;
type DirectoryStringInnerOwned = Either<PrintableStringValueOwned, UTF8StringValueOwned>;

impl<'a> PolyfillClone for DirectoryStringValue<'a> {
    fn clone(&self) -> Self {
        match self {
            DirectoryStringValue::PrintableString(s) => DirectoryStringValue::PrintableString(PolyfillClone::clone(s)),
            DirectoryStringValue::UTF8String(s) => DirectoryStringValue::UTF8String(PolyfillClone::clone(s)),
        }
    }
}

impl<'a> View for DirectoryStringValue<'a> {
    type V = SpecDirectoryStringValue;

    closed spec fn view(&self) -> Self::V {
        match self {
            DirectoryStringValue::PrintableString(s) => SpecDirectoryStringValue::PrintableString(s@),
            DirectoryStringValue::UTF8String(s) => SpecDirectoryStringValue::UTF8String(s@),
        }
    }
}

impl View for DirectoryStringOwned {
    type V = SpecDirectoryStringValue;

    closed spec fn view(&self) -> Self::V {
        match self {
            DirectoryStringOwned::PrintableString(s) => SpecDirectoryStringValue::PrintableString(s@),
            DirectoryStringOwned::UTF8String(s) => SpecDirectoryStringValue::UTF8String(s@),
        }
    }
}

impl SpecFrom<SpecDirectoryStringInner> for SpecDirectoryStringValue {
    open spec fn spec_from(inner: SpecDirectoryStringInner) -> Self {
        match inner {
            Either::Left(s) => SpecDirectoryStringValue::PrintableString(s),
            Either::Right(s) => SpecDirectoryStringValue::UTF8String(s),
        }
    }
}

impl SpecFrom<SpecDirectoryStringValue> for SpecDirectoryStringInner {
    open spec fn spec_from(inner: SpecDirectoryStringValue) -> Self {
        match inner {
            SpecDirectoryStringValue::PrintableString(s) => Either::Left(s),
            SpecDirectoryStringValue::UTF8String(s) => Either::Right(s),
        }
    }
}

impl<'a> From<DirectoryStringInner<'a>> for DirectoryStringValue<'a> {
    fn ex_from(inner: DirectoryStringInner<'a>) -> Self {
        match inner {
            Either::Left(s) => DirectoryStringValue::PrintableString(s),
            Either::Right(s) => DirectoryStringValue::UTF8String(s),
        }
    }
}

impl<'a> From<DirectoryStringValue<'a>> for DirectoryStringInner<'a> {
    fn ex_from(inner: DirectoryStringValue<'a>) -> Self {
        match inner {
            DirectoryStringValue::PrintableString(s) => Either::Left(s),
            DirectoryStringValue::UTF8String(s) => Either::Right(s),
        }
    }
}

impl From<DirectoryStringInnerOwned> for DirectoryStringOwned {
    fn ex_from(inner: DirectoryStringInnerOwned) -> Self {
        match inner {
            Either::Left(s) => DirectoryStringOwned::PrintableString(s),
            Either::Right(s) => DirectoryStringOwned::UTF8String(s),
        }
    }
}

impl From<DirectoryStringOwned> for DirectoryStringInnerOwned {
    fn ex_from(inner: DirectoryStringOwned) -> Self {
        match inner {
            DirectoryStringOwned::PrintableString(s) => Either::Left(s),
            DirectoryStringOwned::UTF8String(s) => Either::Right(s),
        }
    }
}

#[derive(Debug, View)]
pub struct DirectoryStringMapper;

impl SpecIso for DirectoryStringMapper {
    type Src = SpecDirectoryStringInner;
    type Dst = SpecDirectoryStringValue;

    proof fn spec_iso(s: Self::Src) {}
    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl Iso for DirectoryStringMapper {
    type Src<'a> = DirectoryStringInner<'a>;
    type Dst<'a> = DirectoryStringValue<'a>;

    type SrcOwned = DirectoryStringInnerOwned;
    type DstOwned = DirectoryStringOwned;
}

}
