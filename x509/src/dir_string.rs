use vstd::prelude::*;

use crate::asn1::*;
use crate::asn1::vest::*;

use crate::utils::*;

verus! {

pub type DirectoryStringCombinator = Mapped<OrdChoice<ASN1<PrintableString>, ASN1<UTF8String>>, DirectoryStringMapper>;

pub fn x509_directory_string() -> DirectoryStringCombinator {
    Mapped {
        inner: OrdChoice::new(
            ASN1(PrintableString),
            ASN1(UTF8String),
        ),
        mapper: DirectoryStringMapper,
    }
}

pub enum SpecDirectoryString {
    PrintableString(SpecPrintableStringValue),
    UTF8String(SpecUTF8StringValue),
}

#[derive(Debug)]
pub enum DirectoryString<'a> {
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

impl<'a> PolyfillClone for DirectoryString<'a> {
    fn clone(&self) -> Self {
        match self {
            DirectoryString::PrintableString(s) => DirectoryString::PrintableString(PolyfillClone::clone(s)),
            DirectoryString::UTF8String(s) => DirectoryString::UTF8String(PolyfillClone::clone(s)),
        }
    }
}

impl<'a> View for DirectoryString<'a> {
    type V = SpecDirectoryString;

    closed spec fn view(&self) -> Self::V {
        match self {
            DirectoryString::PrintableString(s) => SpecDirectoryString::PrintableString(s@),
            DirectoryString::UTF8String(s) => SpecDirectoryString::UTF8String(s@),
        }
    }
}

impl View for DirectoryStringOwned {
    type V = SpecDirectoryString;

    closed spec fn view(&self) -> Self::V {
        match self {
            DirectoryStringOwned::PrintableString(s) => SpecDirectoryString::PrintableString(s@),
            DirectoryStringOwned::UTF8String(s) => SpecDirectoryString::UTF8String(s@),
        }
    }
}

impl SpecFrom<SpecDirectoryStringInner> for SpecDirectoryString {
    open spec fn spec_from(inner: SpecDirectoryStringInner) -> Self {
        match inner {
            Either::Left(s) => SpecDirectoryString::PrintableString(s),
            Either::Right(s) => SpecDirectoryString::UTF8String(s),
        }
    }
}

impl SpecFrom<SpecDirectoryString> for SpecDirectoryStringInner {
    open spec fn spec_from(inner: SpecDirectoryString) -> Self {
        match inner {
            SpecDirectoryString::PrintableString(s) => Either::Left(s),
            SpecDirectoryString::UTF8String(s) => Either::Right(s),
        }
    }
}

impl<'a> From<DirectoryStringInner<'a>> for DirectoryString<'a> {
    fn ex_from(inner: DirectoryStringInner<'a>) -> Self {
        match inner {
            Either::Left(s) => DirectoryString::PrintableString(s),
            Either::Right(s) => DirectoryString::UTF8String(s),
        }
    }
}

impl<'a> From<DirectoryString<'a>> for DirectoryStringInner<'a> {
    fn ex_from(inner: DirectoryString<'a>) -> Self {
        match inner {
            DirectoryString::PrintableString(s) => Either::Left(s),
            DirectoryString::UTF8String(s) => Either::Right(s),
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

#[derive(Debug)]
pub struct DirectoryStringMapper;
impl_trivial_view!(DirectoryStringMapper);
impl_trivial_poly_clone!(DirectoryStringMapper);

impl SpecIso for DirectoryStringMapper {
    type Src = SpecDirectoryStringInner;
    type Dst = SpecDirectoryString;

    proof fn spec_iso(s: Self::Src) {}
    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl Iso for DirectoryStringMapper {
    type Src<'a> = DirectoryStringInner<'a>;
    type Dst<'a> = DirectoryString<'a>;

    type SrcOwned = DirectoryStringInnerOwned;
    type DstOwned = DirectoryStringOwned;
}

}
