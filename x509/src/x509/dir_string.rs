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
pub type DirectoryStringInner = Mapped<OrdChoice<ASN1<PrintableString>, ASN1<UTF8String>>, DirectoryStringMapper>;

wrap_combinator! {
    struct DirectoryString: DirectoryStringInner =>
        SpecDirectoryStringValue,
        DirectoryStringValue<'a>,
        DirectoryStringOwned
    = Mapped {
            inner: OrdChoice(
                ASN1(PrintableString),
                ASN1(UTF8String),
            ),
            mapper: DirectoryStringMapper,
        };
}

#[derive(Debug, View, PolyfillClone)]
pub enum DirectoryStringPoly<PS, US> {
    PrintableString(PS),
    UTF8String(US),
}

pub type SpecDirectoryStringValue = DirectoryStringPoly<SpecPrintableStringValue, SpecUTF8StringValue>;
pub type DirectoryStringValue<'a> = DirectoryStringPoly<PrintableStringValue<'a>, UTF8StringValue<'a>>;
pub type DirectoryStringOwned = DirectoryStringPoly<PrintableStringValueOwned, UTF8StringValueOwned>;

type DirectoryStringFrom<PS, US> = Either<PS, US>;

impl<PS, US> SpecFrom<DirectoryStringFrom<PS, US>> for DirectoryStringPoly<PS, US> {
    open spec fn spec_from(inner: DirectoryStringFrom<PS, US>) -> Self {
        match inner {
            Either::Left(s) => DirectoryStringPoly::PrintableString(s),
            Either::Right(s) => DirectoryStringPoly::UTF8String(s),
        }
    }
}

impl<PS, US> SpecFrom<DirectoryStringPoly<PS, US>> for DirectoryStringFrom<PS, US> {
    open spec fn spec_from(inner: DirectoryStringPoly<PS, US>) -> Self {
        match inner {
            DirectoryStringPoly::PrintableString(s) => Either::Left(s),
            DirectoryStringPoly::UTF8String(s) => Either::Right(s),
        }
    }
}

impl<PS: View, US: View> From<DirectoryStringFrom<PS, US>> for DirectoryStringPoly<PS, US> {
    fn ex_from(inner: DirectoryStringFrom<PS, US>) -> Self {
        match inner {
            Either::Left(s) => DirectoryStringPoly::PrintableString(s),
            Either::Right(s) => DirectoryStringPoly::UTF8String(s),
        }
    }
}

impl<PS: View, US: View> From<DirectoryStringPoly<PS, US>> for DirectoryStringFrom<PS, US> {
    fn ex_from(inner: DirectoryStringPoly<PS, US>) -> Self {
        match inner {
            DirectoryStringPoly::PrintableString(s) => Either::Left(s),
            DirectoryStringPoly::UTF8String(s) => Either::Right(s),
        }
    }
}

#[derive(Debug, View)]
pub struct DirectoryStringMapper;

impl SpecIso for DirectoryStringMapper {
    type Src = DirectoryStringFrom<SpecPrintableStringValue, SpecUTF8StringValue>;
    type Dst = DirectoryStringPoly<SpecPrintableStringValue, SpecUTF8StringValue>;

    proof fn spec_iso(s: Self::Src) {
        let _ = Self::Src::spec_from(Self::Dst::spec_from(s));
    }

    proof fn spec_iso_rev(s: Self::Dst) {
        let _ = Self::Dst::spec_from(Self::Src::spec_from(s));
    }
}

impl Iso for DirectoryStringMapper {
    type Src<'a> = DirectoryStringFrom<PrintableStringValue<'a>, UTF8StringValue<'a>>;
    type Dst<'a> = DirectoryStringPoly<PrintableStringValue<'a>, UTF8StringValue<'a>>;

    type SrcOwned = DirectoryStringFrom<PrintableStringValueOwned, UTF8StringValueOwned>;
    type DstOwned = DirectoryStringPoly<PrintableStringValueOwned, UTF8StringValueOwned>;
}

}
