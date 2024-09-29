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
    ord_choice_type!(
        ASN1<PrintableString>,
        ASN1<UTF8String>,
        ASN1<IA5String>,
        placeholder_type!(),
        placeholder_type!(),
        placeholder_type!(),
    ),
    DirectoryStringMapper>;

wrap_combinator! {
    pub struct DirectoryString: DirectoryStringInner =>
        spec SpecDirectoryStringValue,
        exec<'a> DirectoryStringValue<'a>,
        owned DirectoryStringValueOwned,
    = Mapped {
            inner: ord_choice!(
                ASN1(PrintableString),
                ASN1(UTF8String),
                ASN1(IA5String),
                placeholder!(TELETEX_STRING),
                placeholder!(UNIVERSAL_STRING),
                placeholder!(BMP_STRING),
            ),
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
            inj_ord_choice_pat!(s, *, *, *, *, *) => DirectoryStringPoly::PrintableString(s),
            inj_ord_choice_pat!(*, s, *, *, *, *) => DirectoryStringPoly::UTF8String(s),
            inj_ord_choice_pat!(*, *, s, *, *, *) => DirectoryStringPoly::IA5String(s),
            inj_ord_choice_pat!(*, *, *, s, *, *) => DirectoryStringPoly::TeletexString(s),
            inj_ord_choice_pat!(*, *, *, *, s, *) => DirectoryStringPoly::UniversalString(s),
            inj_ord_choice_pat!(*, *, *, *, *, s) => DirectoryStringPoly::BMPString(s),
        }
    }

    backward(y) {
        match y {
            DirectoryStringPoly::PrintableString(s) => inj_ord_choice_result!(s, *, *, *, *, *),
            DirectoryStringPoly::UTF8String(s) => inj_ord_choice_result!(*, s, *, *, *, *),
            DirectoryStringPoly::IA5String(s) => inj_ord_choice_result!(*, *, s, *, *, *),
            DirectoryStringPoly::TeletexString(s) => inj_ord_choice_result!(*, *, *, s, *, *),
            DirectoryStringPoly::UniversalString(s) => inj_ord_choice_result!(*, *, *, *, s, *),
            DirectoryStringPoly::BMPString(s) => inj_ord_choice_result!(*, *, *, *, *, s),
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
                assert_eq!(s, "ruby-lang");
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
                assert_eq!(s, "Google Trust Services LLC");
            }
            _ => panic!("{:?}", parsed),
        }
    }
}
