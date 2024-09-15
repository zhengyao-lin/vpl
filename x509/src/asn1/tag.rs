use vstd::prelude::*;

use super::vest::*;

verus! {

#[derive(Debug)]
pub struct Tag {
    pub class: TagClass,
    pub form: TagForm,

    /// Currently we only support tag numbers up to 31
    /// Larger tag numbers require the long form of tags
    pub num: u8,
}

#[derive(Debug)]
pub enum TagClass {
    Universal,
    Application,
    ContextSpecific,
    Private,
}

#[derive(Debug)]
pub enum TagForm {
    Primitive,
    Constructed,
}

impl View for Tag {
    type V = Tag;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

pub struct TagParser;

impl View for TagParser {
    type V = TagParser;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecCombinator for TagParser {
    type SpecResult = Tag;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        if s.len() == 0 {
            Err(())
        } else {
            let class_num = s[0] >> 6 & 0b11;
            let class = if class_num == 0 {
                TagClass::Universal
            } else if class_num == 1 {
                TagClass::Application
            } else if class_num == 2 {
                TagClass::ContextSpecific
            } else {
                TagClass::Private
            };

            let form_num = s[0] >> 5 & 1;
            let form = if form_num == 0 {
                TagForm::Primitive
            } else {
                TagForm::Constructed
            };

            Ok((1, Tag {
                class,
                form,
                num: s[0] & 0b11111,
            }))
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {}

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        let class: u8 = match v.class {
            TagClass::Universal => 0,
            TagClass::Application => 1,
            TagClass::ContextSpecific => 2,
            _ => 3,
        };

        let form: u8 = match v.form {
            TagForm::Primitive => 0,
            _ => 1,
        };

        if v.num > 0b11111 {
            Err(())
        } else {
            Ok(seq![(class << 6) | (form << 5) | (v.num & 0b11111)])
        }
    }
}

impl SecureSpecCombinator for TagParser {
    open spec fn spec_is_prefix_secure() -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        let class_num: u8 = match v.class {
            TagClass::Universal => 0,
            TagClass::Application => 1,
            TagClass::ContextSpecific => 2,
            _ => 3,
        };

        let form_num: u8 = match v.form {
            TagForm::Primitive => 0,
            _ => 1,
        };

        let num = v.num;

        // Restate parse(serialize(v)) = v, but purely in BV
        assert(
            0 <= class_num < 4 &&
            0 <= form_num < 2 &&
            0 <= num <= 0b11111 ==> {
            let ser = (class_num << 6) | (form_num << 5) | (num & 0b11111);
            &&& ser >> 6 & 0b11 == class_num
            &&& ser >> 5 & 1 == form_num
            &&& ser & 0b11111 == num
        }) by (bit_vector);
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        let tag = buf[0];

        // Restate serialize(parse(v)) = v, but purely in BV
        assert(
            (tag >> 6 & 0b11) << 6 | (tag >> 5 & 1) << 5 | ((tag & 0b11111) & 0b11111) == tag
        ) by (bit_vector);

        // Some bound facts
        assert(tag >> 6 & 0b11 < 4) by (bit_vector);
        assert(tag >> 5 & 1 < 2) by (bit_vector);
        assert(tag & 0b11111 <= 0b11111) by (bit_vector);

        if let Ok((n, v)) = self.spec_parse(buf) {
            let ser = self.spec_serialize(v).unwrap();
            assert(ser =~= buf.subrange(0, 1));
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {}
}

impl Combinator for TagParser {
    type Result<'a> = Tag;
    type Owned = Tag;

    open spec fn spec_length(&self) -> Option<usize> {
        Some(1)
    }

    fn length(&self) -> Option<usize> {
        Some(1)
    }

    fn exec_is_prefix_secure() -> bool {
        true
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ()>) {
        if s.len() == 0 {
            return Err(());
        } else {
            let class_num = s[0] >> 6 & 0b11;
            let class = if class_num == 0 {
                TagClass::Universal
            } else if class_num == 1 {
                TagClass::Application
            } else if class_num == 2 {
                TagClass::ContextSpecific
            } else {
                TagClass::Private
            };

            let form_num = s[0] >> 5 & 1;
            let form = if form_num == 0 {
                TagForm::Primitive
            } else {
                TagForm::Constructed
            };

            Ok((1, Tag {
                class,
                form,
                num: s[0] & 0b11111,
            }))
        }
    }
    
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, ()>) {
        let class: u8 = match v.class {
            TagClass::Universal => 0,
            TagClass::Application => 1,
            TagClass::ContextSpecific => 2,
            _ => 3,
        };

        let form: u8 = match v.form {
            TagForm::Primitive => 0,
            _ => 1,
        };

        if v.num > 0b11111 {
            return Err(());
        }

        if pos < data.len() {
            let tag = (class << 6) | (form << 5) | (v.num & 0b11111);
            data.set(pos, tag);
            assert(data@ == seq_splice(old(data)@, pos, seq![tag]));
            Ok(1)
        } else {
            Err(())
        }
    }
}

}
