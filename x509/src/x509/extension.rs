use vstd::prelude::*;

use crate::asn1::*;
use crate::asn1::Boolean;

use crate::common::*;

verus! {

/// Extension  ::=  SEQUENCE  {
///     extnID      OBJECT IDENTIFIER,
///     critical    BOOLEAN DEFAULT FALSE,
///     extnValue   OCTET STRING
/// }
pub type ExtensionInner = Mapped<
    LengthWrapped<
        Depend<
            ASN1<ObjectIdentifier>,
            <ExtensionCont as Continuation>::Output,
            ExtensionCont,
        >,
    >,
    ExtensionMapper>;

pub type ExtensionsInner = SequenceOf<ASN1<Extension>>;

wrap_combinator! {
    pub struct Extension: ExtensionInner =>
        spec SpecExtensionValue,
        exec<'a> ExtensionValue<'a>,
        owned ExtensionValueOwned,
    = Mapped {
            inner: LengthWrapped(Depend {
                fst: ASN1(ObjectIdentifier),
                snd: ExtensionCont,
                spec_snd: Ghost(|i| ExtensionCont::spec_apply(i)),
            }),
            mapper: ExtensionMapper,
        };
}

asn1_tagged!(Extension, TagValue {
    class: TagClass::Universal,
    form: TagForm::Constructed,
    num: 0x10,
});

wrap_combinator! {
    pub struct Extensions: ExtensionsInner = SequenceOf(ASN1(Extension));
}

asn1_tagged!(Extensions, TagValue {
    class: TagClass::Universal,
    form: TagForm::Constructed,
    num: 0x10,
});

mapper! {
    pub struct ExtensionMapper;

    for <Id, AKI, Other>
    from ExtensionFrom where type ExtensionFrom<Id, AKI, Other> =
        (Id, PairValue<OptionDeep<bool>, ord_choice_result!(AKI, Other)>);
    to ExtensionPoly where pub struct ExtensionPoly<Id, AKI, Other> {
        pub id: Id,
        pub critical: OptionDeep<bool>,
        pub param: ExtensionParamPoly<AKI, Other>,
    }

    spec SpecExtensionValue with <SpecObjectIdentifierValue, Seq<u8>, Seq<u8>>;
    exec ExtensionValue<'a> with <ObjectIdentifierValue, &'a [u8], &'a [u8]>;
    owned ExtensionValueOwned with <ObjectIdentifierValueOwned, Vec<u8>, Vec<u8>>;

    forward(x) {
        ExtensionPoly {
            id: x.0,
            critical: x.1.0,
            param: match x.1.1 {
                inj_ord_choice_pat!(p, *) => ExtensionParamPoly::AuthorityKeyIdentifier(p),
                inj_ord_choice_pat!(*, p) => ExtensionParamPoly::Other(p),
            },
        }
    }

    backward(y) {
        (y.id, PairValue(y.critical, match y.param {
            ExtensionParamPoly::AuthorityKeyIdentifier(p) => inj_ord_choice_result!(p, *),
            ExtensionParamPoly::Other(p) => inj_ord_choice_result!(*, p),
        }))
    }
}

#[derive(Debug, View, PolyfillClone)]
pub enum ExtensionParamPoly<AKI, Other> {
    AuthorityKeyIdentifier(AKI),
    Other(Other),
}

// pub type SpecExtensionParamValue = ExtensionParamPoly<Seq<u8>, Seq<u8>>;
// pub type ExtensionParamValue<'a> = ExtensionParamPoly<&'a [u8], &'a [u8]>;
// pub type ExtensionParamValueOwned = ExtensionParamPoly<Vec<u8>, Vec<u8>>;

#[derive(Debug, View)]
pub struct ExtensionCont;

impl ExtensionCont {
    pub open spec fn spec_apply(i: SpecObjectIdentifierValue) -> <ExtensionCont as Continuation>::Output {
        let c1 = (i =~= seq![ 2 as UInt, 5, 29, 35 ]);
        let c2 = !(i =~= seq![ 2 as UInt, 5, 29, 35 ]);
        Optional(
            ASN1(Boolean),
            ord_choice!(
                Cond { cond: c1, inner: ASN1(OctetString) },
                Cond { cond: c2, inner: ASN1(OctetString) },
            ),
        )
    }
}

impl Continuation for ExtensionCont {
    type Input<'a> = ObjectIdentifierValue;
    type Output = Optional<ASN1<Boolean>, ord_choice_type!(
        Cond<ASN1<OctetString>>,
        Cond<ASN1<OctetString>>,
    )>;

    fn apply<'a>(&self, i: Self::Input<'a>) -> (o: Self::Output) {
        Optional(
            ASN1(Boolean),
            ord_choice!(
                Cond { cond: i.is(&[ 2, 5, 29, 35 ]), inner: ASN1(OctetString) },
                Cond { cond: !i.is(&[ 2, 5, 29, 35 ]), inner: ASN1(OctetString) },
            ),
        )
    }

    open spec fn requires<'a>(&self, i: Self::Input<'a>) -> bool {
        true
    }

    open spec fn ensures<'a>(&self, i: Self::Input<'a>, o: Self::Output) -> bool {
        o@ == Self::spec_apply(i@)
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
            let _ = ASN1(Extension).parse(&[]);
            let _ = ASN1(Extensions).parse(&[]);
        }
    }

    #[test]
    fn sanity() {
        assert!(ASN1(Extension).parse(&[
            0x30, 0x1D, 0x06, 0x03, 0x55, 0x1D, 0x0E, 0x04, 0x16, 0x04, 0x14, 0xE4, 0xAF, 0x2B, 0x26, 0x71, 0x1A, 0x2B, 0x48, 0x27, 0x85, 0x2F, 0x52, 0x66, 0x2C, 0xEF, 0xF0, 0x89, 0x13, 0x71, 0x3E,
        ]).is_ok());

        assert!(ASN1(Extensions).parse(&[
            0x30, 0x40, 0x30, 0x0E, 0x06, 0x03, 0x55, 0x1D, 0x0F, 0x01, 0x01, 0xFF, 0x04, 0x04, 0x03, 0x02, 0x01, 0x86, 0x30, 0x0F, 0x06, 0x03, 0x55, 0x1D, 0x13, 0x01, 0x01, 0xFF, 0x04, 0x05, 0x30, 0x03, 0x01, 0x01, 0xFF, 0x30, 0x1D, 0x06, 0x03, 0x55, 0x1D, 0x0E, 0x04, 0x16, 0x04, 0x14, 0xE4, 0xAF, 0x2B, 0x26, 0x71, 0x1A, 0x2B, 0x48, 0x27, 0x85, 0x2F, 0x52, 0x66, 0x2C, 0xEF, 0xF0, 0x89, 0x13, 0x71, 0x3E,
        ]).is_ok());
    }
}
