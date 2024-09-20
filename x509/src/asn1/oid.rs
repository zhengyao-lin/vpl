use vstd::prelude::*;

use crate::common::*;

use super::bounds::*;
use super::base128::*;
use super::len::*;
use super::tag::*;

verus! {

/// Combinator for ASN.1 Object Identifier
#[derive(Debug, View)]
pub struct ObjectIdentifier;

asn1_tagged!(ObjectIdentifier, TagValue {
    class: TagClass::Universal,
    form: TagForm::Primitive,
    num: 0x06,
});

pub type SpecObjectIdentifierValue = Seq<UInt>;
pub type ObjectIdentifierValue = VecDeep<UInt>;
pub type ObjectIdentifierValueOwned = VecDeep<UInt>;

impl ObjectIdentifier {
    /// First byte of an OID is 40 * arc1 + arc2
    pub open spec fn parse_first_two_arcs(byte: u8) -> Option<(UInt, UInt)> {
        let arc1 = byte / 40;
        let arc2 = byte % 40;

        if arc1 <= 2 && arc2 <= 39 {
            Some((arc1 as UInt, arc2 as UInt))
        } else {
            None
        }
    }

    pub open spec fn serialize_first_two_arcs(arc1: UInt, arc2: UInt) -> Option<u8> {
        if arc1 <= 2 && arc2 <= 39 {
            Some((arc1 * 40 + arc2) as u8)
        } else {
            None
        }
    }

    proof fn lemma_serialize_parse_first_two_arcs(arc1: UInt, arc2: UInt)
        ensures
            Self::serialize_first_two_arcs(arc1, arc2) matches Some(byte) ==>
                Self::parse_first_two_arcs(byte) == Some((arc1, arc2))
    {}

    proof fn lemma_parse_serialize_first_two_arcs(byte: u8)
        ensures
            Self::parse_first_two_arcs(byte) matches Some((arc1, arc2)) ==>
                Self::serialize_first_two_arcs(arc1, arc2) == Some(byte)
    {}
}

impl SpecCombinator for ObjectIdentifier {
    type SpecResult = SpecObjectIdentifierValue;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        match new_spec_object_identifier_inner().spec_parse(s) {
            Ok((len, (_, (first, rest_arcs)))) =>
                match Self::parse_first_two_arcs(first) {
                    Some((arc1, arc2)) => {
                        Ok((len, seq![ arc1, arc2 ] + rest_arcs))
                    },
                    None => Err(()),
                }

            Err(..) => Err(()),
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {}

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        if v.len() < 2 {
            Err(())
        } else {
            match Self::serialize_first_two_arcs(v[0], v[1]) {
                Some(first_byte) => {
                    let rest_arcs = v.skip(2);

                    // Compute the inner length first
                    // TODO: how to avoid this?
                    match (U8, Repeat(Base128UInt)).spec_serialize((first_byte, rest_arcs)) {
                        Ok(buf) =>
                            new_spec_object_identifier_inner().spec_serialize((buf.len() as LengthValue, (first_byte, rest_arcs))),
                        Err(..) => Err(())
                    }
                },
                None => Err(()),
            }
        }
    }
}

impl SecureSpecCombinator for ObjectIdentifier {
    open spec fn spec_is_prefix_secure() -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        if let Ok(b) = self.spec_serialize(v) {
            let first_byte = Self::serialize_first_two_arcs(v[0], v[1]).unwrap();
            let rest_arcs = v.skip(2);
            let buf = (U8, Repeat(Base128UInt)).spec_serialize((first_byte, rest_arcs)).unwrap();

            new_spec_object_identifier_inner().theorem_serialize_parse_roundtrip((buf.len() as LengthValue, (first_byte, rest_arcs)));
            Self::lemma_serialize_parse_first_two_arcs(v[0], v[1]);

            let (len, v2) = self.spec_parse(b).unwrap();
            assert(len == b.len() as usize);
            assert(v2 =~= v);
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if let Ok((len, v)) = self.spec_parse(buf) {
            let (_, (_, (first_byte, rest_arcs))) = new_spec_object_identifier_inner().spec_parse(buf).unwrap();

            new_spec_object_identifier_inner().theorem_parse_serialize_roundtrip(buf);
            Self::lemma_parse_serialize_first_two_arcs(first_byte);

            assert(v.skip(2) =~= rest_arcs);

            let buf2 = self.spec_serialize(v).unwrap();
            assert(buf2 =~= buf.subrange(0, len as int));
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        new_spec_object_identifier_inner().lemma_prefix_secure(s1, s2);
    }
}

impl Combinator for ObjectIdentifier {
    type Result<'a> = ObjectIdentifierValue;
    type Owned = ObjectIdentifierValueOwned;

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
        if let Ok((len, (_, (first, mut rest_arcs)))) = new_object_identifier_inner().parse(s) {
            let arc1 = first / 40;
            let arc2 = first % 40;

            if arc1 > 2 || arc2 > 39 {
                return Err(());
            }

            let mut res = VecDeep::from_vec(vec![ arc1 as UInt, arc2 as UInt ]);
            res.append(&mut rest_arcs);

            assert(res@ == self.spec_parse(s@).unwrap().1);

            Ok((len, res))
        } else {
            Err(())
        }
    }

    fn serialize(&self, mut v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, ()>) {
        let ghost old_v = v@;

        if v.len() < 2 {
            return Err(());
        }

        if *v.get(0) > 2 || *v.get(1) > 39 {
            return Err(());
        }

        let first_byte = *v.get(0) as u8 * 40 + *v.get(1) as u8;

        let rest_arcs_inner = v.split_off(2);

        // Need to figure out the content length first
        // TODO: this seems inefficient
        let rest_arcs_cloned = PolyfillClone::clone(&rest_arcs_inner);
        let rest_arcs = rest_arcs_inner;

        if let Ok(len) = (U8, Repeat(Base128UInt)).serialize((first_byte, rest_arcs_cloned), data, pos) {
            let ghost data2 = data@;

            if let Ok(len2) = new_object_identifier_inner().serialize((len as LengthValue, (first_byte, rest_arcs)), data, pos) {
                // assert(data@ == seq_splice(old(data)@, pos, b));
                // assert(len2 >= len);

                if pos.checked_add(len2).is_some() && pos + len2 <= data.len() {
                    assert(rest_arcs_cloned@ == old_v.skip(2));
                    assert(data@ =~= seq_splice(old(data)@, pos, self.spec_serialize(old_v).unwrap()));

                    return Ok(len2);
                }
            }
        }

        Err(())
    }
}

/// The function |i| AndThen(Bytes(i as usize), (U8, Repeat(Base128UInt)))
struct OIDCont;

impl Continuation for OIDCont {
    type Input<'a> = LengthValue;
    type Output = AndThen<Bytes, (U8, Repeat<Base128UInt>)>;

    fn apply<'a>(&self, i: Self::Input<'a>) -> (o: Self::Output) {
        AndThen(Bytes(i as usize), (U8, Repeat(Base128UInt)))
    }

    open spec fn requires<'a>(&self, i: Self::Input<'a>) -> bool {
        true
    }

    open spec fn ensures<'a>(&self, i: Self::Input<'a>, o: Self::Output) -> bool {
        o == AndThen(Bytes(i as usize), (U8, Repeat(Base128UInt)))
    }
}

/// The inner version parses a length first
/// then read a single byte (for the first two arcs)
/// and then repeatedly read a sequence of Base128UInt's
type SpecObjectIdentifierInner = SpecDepend<Length, AndThen<Bytes, (U8, Repeat<Base128UInt>)>>;
type ObjectIdentifierInner = Depend<Length, AndThen<Bytes, (U8, Repeat<Base128UInt>)>, OIDCont>;

pub open spec fn new_spec_object_identifier_inner() -> SpecObjectIdentifierInner {
    SpecDepend {
        fst: Length,
        snd: |l| {
            AndThen(Bytes(l as usize), (U8, Repeat(Base128UInt)))
        },
    }
}

fn new_object_identifier_inner() -> (res: ObjectIdentifierInner)
    ensures res@ == new_spec_object_identifier_inner()
{
    Depend {
        fst: Length,
        snd: OIDCont,
        spec_snd: Ghost(|l| {
            AndThen(Bytes(l as usize), (U8, Repeat(Base128UInt)))
        }),
    }
}

}
