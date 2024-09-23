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
pub type DirectoryStringInner = Mapped<
        OrdChoice<ASN1<PrintableString>,
        OrdChoice<ASN1<UTF8String>,
        OrdChoice<ASN1<IA5String>,
        OrdChoice<ASN1<ImplicitTag<OctetString>>,
        OrdChoice<ASN1<ImplicitTag<OctetString>>,
        ASN1<ImplicitTag<OctetString>>,
    >>>>>, DirectoryStringMapper>;

wrap_combinator! {
    struct DirectoryString: DirectoryStringInner =>
        spec SpecDirectoryStringValue,
        exec<'a> DirectoryStringValue<'a>,
        owned DirectoryStringValueOwned,
    = Mapped {
            inner:
                OrdChoice(ASN1(PrintableString),
                OrdChoice(ASN1(UTF8String),
                OrdChoice(ASN1(IA5String),
                OrdChoice(ASN1(ImplicitTag(TagValue {
                    class: TagClass::Universal,
                    form: TagForm::Primitive,
                    num: 0x14, // TeletexString
                }, OctetString)),
                OrdChoice(ASN1(ImplicitTag(TagValue {
                    class: TagClass::Universal,
                    form: TagForm::Primitive,
                    num: 0x1c, // UniversalString
                }, OctetString)),
                ASN1(ImplicitTag(TagValue {
                    class: TagClass::Universal,
                    form: TagForm::Primitive,
                    num: 0x1e, // BMPString
                }, OctetString)),
                ))))),
            mapper: DirectoryStringMapper,
        };
}

mapper! {
    pub struct DirectoryStringMapper;

    for <PS, US, IS, TS, UNS, BS>

    from DirectoryStringFrom where
        type DirectoryStringFrom<PS, US, IS, TS, UNS, BS> = Either<PS, Either<US, Either<IS, Either<TS, Either<UNS, BS>>>>>;

    to DirectoryStringPoly where
        #[derive(Eq, PartialEq)]
        pub enum DirectoryStringPoly<PS, US, IS, TS, UNS, BS> {
            PrintableString(PS),
            UTF8String(US),
            IA5String(IS),
            TeletexString(TS),
            UniversalString(UNS),
            BMPString(BS),
        }

    spec SpecDirectoryStringValue with <SpecPrintableStringValue, SpecUTF8StringValue, SpecIA5StringValue, Seq<u8>, Seq<u8>, Seq<u8>>;
    exec DirectoryStringValue<'a> with <PrintableStringValue<'a>, UTF8StringValue<'a>, IA5StringValue<'a>, &'a [u8], &'a [u8], &'a [u8]>;
    owned DirectoryStringValueOwned with <PrintableStringValueOwned, UTF8StringValueOwned, IA5StringValueOwned, Vec<u8>, Vec<u8>, Vec<u8>>;

    forward(x) {
        match x {
            Either::Left(s) => DirectoryStringPoly::PrintableString(s),
            Either::Right(Either::Left(s)) => DirectoryStringPoly::UTF8String(s),
            Either::Right(Either::Right(Either::Left(s))) => DirectoryStringPoly::IA5String(s),
            Either::Right(Either::Right(Either::Right(Either::Left(s)))) => DirectoryStringPoly::TeletexString(s),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(s))))) => DirectoryStringPoly::UniversalString(s),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(s))))) => DirectoryStringPoly::BMPString(s),
        }
    }

    backward(y) {
        match y {
            DirectoryStringPoly::PrintableString(s) => Either::Left(s),
            DirectoryStringPoly::UTF8String(s) => Either::Right(Either::Left(s)),
            DirectoryStringPoly::IA5String(s) => Either::Right(Either::Right(Either::Left(s))),
            DirectoryStringPoly::TeletexString(s) => Either::Right(Either::Right(Either::Right(Either::Left(s)))),
            DirectoryStringPoly::UniversalString(s) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(s))))),
            DirectoryStringPoly::BMPString(s) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(s))))),
        }
    }
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
