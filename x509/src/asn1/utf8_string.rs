use vstd::prelude::*;
use vstd::vstd::slice::slice_subrange;

use polyfill::*;

use crate::common::*;

use super::len::*;
use super::tag::*;

verus! {

/// Combainator for UTF8String in ASN.1
#[derive(Debug, View)]
pub struct UTF8String;

pub type SpecUTF8StringValue = Seq<char>;
pub type UTF8StringValue<'a> = &'a str;
pub type UTF8StringValueOwned = String;

impl ASN1Tagged for UTF8String {
    open spec fn spec_tag(&self) -> TagValue {
        TagValue {
            class: TagClass::Universal,
            form: TagForm::Primitive,
            num: 0x0c,
        }
    }

    fn tag(&self) -> TagValue {
        TagValue {
            class: TagClass::Universal,
            form: TagForm::Primitive,
            num: 0x0c,
        }
    }
}

impl ViewWithASN1Tagged for UTF8String {
    proof fn lemma_view_preserves_tag(&self) {}
}

impl SpecCombinator for UTF8String {
    type SpecResult = SpecUTF8StringValue;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        match Length.spec_parse(s) {
            Ok((n, l)) => {
                if n + l <= usize::MAX && n + l <= s.len() {
                    match spec_parse_utf8(s.skip(n as int).take(l as int)) {
                        Some(parsed) => Ok(((n + l) as usize, parsed)),
                        None => Err(()),
                    }
                } else {
                    Err(())
                }
            }
            Err(()) => Err(()),
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {}

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        let s = spec_serialize_utf8(v);
        match Length.spec_serialize(s.len() as LengthValue) {
            Ok(buf) =>
                if buf.len() + s.len() <= usize::MAX {
                    Ok(buf + s)
                } else {
                    Err(())
                },
            Err(()) => Err(()),
        }
    }
}

impl SecureSpecCombinator for UTF8String {
    open spec fn spec_is_prefix_secure() -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        let s = spec_serialize_utf8(v);

        Length.theorem_serialize_parse_roundtrip(s.len() as LengthValue);
        spec_utf8_serialize_parse_roundtrip(v);

        if let Ok(buf) = Length.spec_serialize(s.len() as LengthValue)  {
            if buf.len() + s.len() <= usize::MAX {
                Length.lemma_prefix_secure(buf, s);
                assert((buf + s).skip(buf.len() as int).take(s.len() as int) == s);
            }
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if let Ok((n, l)) = Length.spec_parse(buf) {
            if n + l <= buf.len() {
                let s = buf.skip(n as int).take(l as int);

                Length.theorem_parse_serialize_roundtrip(buf);
                spec_utf8_parse_serialize_roundtrip(s);
                assert(buf.subrange(0, (n + l) as int) == buf.subrange(0, n as int) + buf.skip(n as int).take(l as int));
            }
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        Length.lemma_prefix_secure(s1, s2);

        if let Ok((n, l)) = Length.spec_parse(s1) {
            if n + l <= s1.len() {
                assert(s1.skip(n as int).take(l as int) =~= (s1 + s2).skip(n as int).take(l as int));
            }
        }
    }
}

impl Combinator for UTF8String {
    type Result<'a> = UTF8StringValue<'a>;
    type Owned = UTF8StringValueOwned;

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
        match Length.parse(s) {
            Ok((n, l)) => {
                if let Some(total_len) = n.checked_add(l as usize) {
                    if total_len <= s.len() {
                        match utf8_to_str(slice_take(slice_subrange(s, n, s.len()), l as usize)) {
                            Some(parsed) => {
                                return Ok((total_len, parsed));
                            },
                            _ => {}
                        }
                    }
                }
            }
            _ => {},
        }

        Err(())
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, ()>) {
        let s = str_to_utf8(v);
        let n = Length.serialize(s.len() as LengthValue, data, pos)?;

        if pos.checked_add(n).is_none() {
            return Err(());
        }

        if (pos + n).checked_add(s.len()).is_none() {
            return Err(());
        }

        if pos + n + s.len() >= data.len() {
            return Err(());
        }

        let ghost data_after_len = data@;

        // No Vec::splice yet in Verus
        for i in 0..s.len()
            invariant
                pos + n + s.len() <= usize::MAX,
                pos + n + s.len() < data.len() == data_after_len.len(),

                data@ =~= seq_splice(data_after_len, (pos + n) as usize, s@.take(i as int)),
        {
            data.set(pos + n + i, s[i]);
        }

        assert(data@ =~= seq_splice(old(data)@, pos, Length.spec_serialize(s@.len() as LengthValue).unwrap() + s@));

        Ok(n + s.len())
    }
}

}
