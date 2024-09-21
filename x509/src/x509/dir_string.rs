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
///     ia5String               IA5String (SIZE (1..MAX))
/// }
///
/// TODO: only supporting PrintableString and UTF8String for now
pub type DirectoryStringInner = Mapped<OrdChoice<ASN1<PrintableString>, OrdChoice<ASN1<UTF8String>, ASN1<IA5String>>>, DirectoryStringMapper>;

wrap_combinator! {
    struct DirectoryString: DirectoryStringInner =>
        spec SpecDirectoryStringValue,
        exec<'a> DirectoryStringValue<'a>,
        owned DirectoryStringValueOwned,
    = Mapped {
            inner: OrdChoice(
                ASN1(PrintableString),
                OrdChoice(
                    ASN1(UTF8String),
                    ASN1(IA5String),
                )
            ),
            mapper: DirectoryStringMapper,
        };
}

#[derive(Debug, View, PolyfillClone)]
pub enum DirectoryStringPoly<PS, US, IS> {
    PrintableString(PS),
    UTF8String(US),
    IA5String(IS),
}

pub type SpecDirectoryStringValue = DirectoryStringPoly<SpecPrintableStringValue, SpecUTF8StringValue, SpecIA5StringValue>;
pub type DirectoryStringValue<'a> = DirectoryStringPoly<PrintableStringValue<'a>, UTF8StringValue<'a>, IA5StringValue<'a>>;
pub type DirectoryStringValueOwned = DirectoryStringPoly<PrintableStringValueOwned, UTF8StringValueOwned, IA5StringValueOwned>;

type DirectoryStringFrom<PS, US, IS> = Either<PS, Either<US, IS>>;

impl<PS, US, IS> SpecFrom<DirectoryStringFrom<PS, US, IS>> for DirectoryStringPoly<PS, US, IS> {
    open spec fn spec_from(inner: DirectoryStringFrom<PS, US, IS>) -> Self {
        match inner {
            Either::Left(s) => DirectoryStringPoly::PrintableString(s),
            Either::Right(Either::Left(s)) => DirectoryStringPoly::UTF8String(s),
            Either::Right(Either::Right(s)) => DirectoryStringPoly::IA5String(s),
        }
    }
}

impl<PS, US, IS> SpecFrom<DirectoryStringPoly<PS, US, IS>> for DirectoryStringFrom<PS, US, IS> {
    open spec fn spec_from(inner: DirectoryStringPoly<PS, US, IS>) -> Self {
        match inner {
            DirectoryStringPoly::PrintableString(s) => Either::Left(s),
            DirectoryStringPoly::UTF8String(s) => Either::Right(Either::Left(s)),
            DirectoryStringPoly::IA5String(s) => Either::Right(Either::Right(s)),
        }
    }
}

impl<PS: View, US: View, IS: View> From<DirectoryStringFrom<PS, US, IS>> for DirectoryStringPoly<PS, US, IS> {
    fn ex_from(inner: DirectoryStringFrom<PS, US, IS>) -> Self {
        match inner {
            Either::Left(s) => DirectoryStringPoly::PrintableString(s),
            Either::Right(Either::Left(s)) => DirectoryStringPoly::UTF8String(s),
            Either::Right(Either::Right(s)) => DirectoryStringPoly::IA5String(s),
        }
    }
}

impl<PS: View, US: View, IS: View> From<DirectoryStringPoly<PS, US, IS>> for DirectoryStringFrom<PS, US, IS> {
    fn ex_from(inner: DirectoryStringPoly<PS, US, IS>) -> Self {
        match inner {
            DirectoryStringPoly::PrintableString(s) => Either::Left(s),
            DirectoryStringPoly::UTF8String(s) => Either::Right(Either::Left(s)),
            DirectoryStringPoly::IA5String(s) => Either::Right(Either::Right(s)),
        }
    }
}

#[derive(Debug, View)]
pub struct DirectoryStringMapper;

impl SpecIso for DirectoryStringMapper {
    type Src = DirectoryStringFrom<SpecPrintableStringValue, SpecUTF8StringValue, SpecIA5StringValue>;
    type Dst = DirectoryStringPoly<SpecPrintableStringValue, SpecUTF8StringValue, SpecIA5StringValue>;

    proof fn spec_iso(s: Self::Src) {
        let _ = Self::Src::spec_from(Self::Dst::spec_from(s));
    }

    proof fn spec_iso_rev(s: Self::Dst) {
        let _ = Self::Dst::spec_from(Self::Src::spec_from(s));
    }
}

impl Iso for DirectoryStringMapper {
    type Src<'a> = DirectoryStringFrom<PrintableStringValue<'a>, UTF8StringValue<'a>, IA5StringValue<'a>>;
    type Dst<'a> = DirectoryStringPoly<PrintableStringValue<'a>, UTF8StringValue<'a>, IA5StringValue<'a>>;

    type SrcOwned = DirectoryStringFrom<PrintableStringValueOwned, UTF8StringValueOwned, IA5StringValueOwned>;
    type DstOwned = DirectoryStringPoly<PrintableStringValueOwned, UTF8StringValueOwned, IA5StringValueOwned>;
}

}
