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

#[derive(Eq, PartialEq, Debug, View, PolyfillClone)]
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

#[cfg(test)]
mod test {
    use super::*;

    verus! {
        /// Check that all trait bounds and preconditions are satisfied
        #[test]
        fn is_combinator() {
            let _ = DirectoryString.parse(&[]);
        }
    }

    #[test]
    fn utf8() {
        assert_eq!(DirectoryString.parse(&[
            0x0C, 0x07, 0x52, 0x75, 0x62, 0x79, 0x20, 0x43, 0x41,
        ]).unwrap().1, DirectoryStringPoly::UTF8String("Ruby CA"));
    }

    #[test]
    fn ia5_string() {
        let parsed = DirectoryString.parse(&[
            0x16, 0x09, 0x72, 0x75, 0x62, 0x79, 0x2D, 0x6C, 0x61, 0x6E, 0x67,
        ]).unwrap().1;

        match parsed {
            DirectoryStringPoly::IA5String(s) => {
                assert_eq!(s.to_string(), Some("ruby-lang".to_string()));
            }
            _ => panic!("{:?}", parsed),
        }
    }

    #[test]
    fn printable_string() {
        let parsed = DirectoryString.parse(&[
            0x13, 0x19, 0x47, 0x6F, 0x6F, 0x67, 0x6C, 0x65, 0x20, 0x54, 0x72, 0x75, 0x73, 0x74, 0x20, 0x53, 0x65, 0x72, 0x76, 0x69, 0x63, 0x65, 0x73, 0x20, 0x4C, 0x4C, 0x43,
        ]).unwrap().1;

        match parsed {
            DirectoryStringPoly::PrintableString(s) => {
                assert_eq!(s.to_string(), Some("Google Trust Services LLC".to_string()));
            }
            _ => panic!("{:?}", parsed),
        }
    }
}
