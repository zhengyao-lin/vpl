/// TODO: maybe refactor this using Refined

use vstd::prelude::*;

use polyfill::*;

use crate::common::*;

use super::octet_string::*;
use super::tag::*;

verus! {

/// Combinator for PrintableString in ASN.1
/// Essentially a wrapper around Octet
/// that checks that each byte is <= 127
#[derive(Debug, View, ViewWithASN1Tagged)]
pub struct PrintableString;

#[derive(Debug, View, PolyfillClone)]
pub struct PrintableStringPoly<T>(pub T);

pub type SpecPrintableStringValue = PrintableStringPoly<Seq<u8>>;
pub type PrintableStringValue<'a> = PrintableStringPoly<&'a [u8]>;
pub type PrintableStringValueOwned = PrintableStringPoly<Vec<u8>>;

impl ASN1Tagged for PrintableString {
    open spec fn spec_tag(&self) -> TagValue {
        TagValue {
            class: TagClass::Universal,
            form: TagForm::Primitive,
            num: 0x13,
        }
    }

    fn tag(&self) -> TagValue {
        TagValue {
            class: TagClass::Universal,
            form: TagForm::Primitive,
            num: 0x13,
        }
    }
}

impl SpecPrintableStringValue {
    pub open spec fn wf(&self) -> bool {
        forall |i| 0 <= i < self.0.len() ==> #[trigger] Self::wf_byte(self.0[i])
    }

    pub open spec fn wf_byte(c: u8) -> bool {
        // https://en.wikipedia.org/wiki/PrintableString
        ||| 65 <= c && c <= 90 // A - Z
        ||| 97 <= c && c <= 122 // a - z
        ||| 48 <= c && c <= 57 // 0 - 9
        ||| c == 32 // space
        ||| 39 <= c && c <= 41 // '()
        ||| 43 <= c && c <= 47 // +,-./
        ||| c == 58 // :
        ||| c == 61 // =
        ||| c == 63 // ?
    }
}

impl<'a> PrintableStringValue<'a> {
    pub fn new(s: &'a [u8]) -> (res: Option<PrintableStringValue<'a>>)
        ensures
            res matches Some(res) ==> res@.wf(),
            res is None ==> !PrintableStringPoly(s@).wf(),
    {
        let res = PrintableStringPoly(s);

        if res.wf() {
            Some(res)
        } else {
            None
        }
    }

    pub fn as_bytes(&self) -> &'a [u8] {
        self.0
    }

    pub fn wf(&self) -> (res: bool)
        ensures res == self@.wf()
    {
        let len = self.0.len();
        for i in 0..len
            invariant
                len == self@.0.len(),
                forall |j| 0 <= j < i ==> #[trigger] SpecPrintableStringValue::wf_byte(self.0[j]),
        {
            if !Self::wf_byte(self.0[i]) {
                return false;
            }
        }
        return true;
    }

    pub fn wf_byte(c: u8) -> (res: bool)
        ensures
            res == SpecPrintableStringValue::wf_byte(c)
    {
        (65 <= c && c <= 90) || // A - Z
        (97 <= c && c <= 122) || // a - z
        (48 <= c && c <= 57) || // 0 - 9
        c == 32 || // space
        39 <= c && c <= 41 || // '()
        43 <= c && c <= 47 || // +,-./
        c == 58 || // :
        c == 61 || // =
        c == 63 // ?
    }
}

impl SpecCombinator for PrintableString {
    type SpecResult = SpecPrintableStringValue;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        match OctetString.spec_parse(s) {
            Ok((len, v)) =>
                if PrintableStringPoly(v).wf() {
                    Ok((len, PrintableStringPoly(v)))
                } else {
                    Err(())
                }
            Err(..) => Err(()),
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {}

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        if v.wf() {
            OctetString.spec_serialize(v.0)
        } else {
            Err(())
        }

    }
}

impl SecureSpecCombinator for PrintableString {
    open spec fn spec_is_prefix_secure() -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        OctetString.theorem_serialize_parse_roundtrip(v.0);
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        OctetString.theorem_parse_serialize_roundtrip(buf);
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        OctetString.lemma_prefix_secure(s1, s2);
    }
}

impl Combinator for PrintableString {
    type Result<'a> = PrintableStringValue<'a>;
    type Owned = PrintableStringValueOwned;

    open spec fn spec_length(&self) -> Option<usize> {
        None
    }

    fn length(&self) -> Option<usize> {
        None
    }

    fn exec_is_prefix_secure() -> bool {
        true
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ()>) {
        let (len, v) = OctetString.parse(s)?;

        if PrintableStringPoly(v).wf() {
            Ok((len, PrintableStringPoly(v)))
        } else {
            Err(())
        }
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, ()>) {
        if v.wf() {
            OctetString.serialize(v.0, data, pos)
        } else {
            Err(())
        }
    }
}

}
