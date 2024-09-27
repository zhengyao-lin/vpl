use vstd::prelude::*;

use crate::asn1::*;

use crate::common::*;

verus! {

#[derive(Debug, View)]
pub struct ExtensionParamCont;

impl ExtensionParamCont {
    pub open spec fn spec_apply(i: SpecObjectIdentifierValue) -> <ExtensionParamCont as Continuation>::Output {
        let c1 = (i =~= seq![ 2 as UInt, 5, 29, 35 ]);
        let c2 = !(i =~= seq![ 2 as UInt, 5, 29, 35 ]);
        Mapped {
            inner: ord_choice!(
                Cond { cond: c1, inner: ASN1(OctetString) },
                Cond { cond: c2, inner: ASN1(OctetString) },
            ),
            mapper: ExtensionParamMapper,
        }
    }
}

impl Continuation for ExtensionParamCont {
    type Input<'a> = ObjectIdentifierValue;
    type Output = Mapped<ord_choice_type!(
        Cond<ASN1<OctetString>>,
        Cond<ASN1<OctetString>>,
    ), ExtensionParamMapper>;

    fn apply<'a>(&self, i: Self::Input<'a>) -> (o: Self::Output) {
        Mapped {
            inner: ord_choice!(
                Cond { cond: i.is(&[ 2, 5, 29, 35 ]), inner: ASN1(OctetString) },
                Cond { cond: !i.is(&[ 2, 5, 29, 35 ]), inner: ASN1(OctetString) },
            ),
            mapper: ExtensionParamMapper,
        }
    }

    open spec fn requires<'a>(&self, i: Self::Input<'a>) -> bool {
        true
    }

    open spec fn ensures<'a>(&self, i: Self::Input<'a>, o: Self::Output) -> bool {
        o@ == Self::spec_apply(i@)
    }
}

mapper! {
    pub struct ExtensionParamMapper;

    for <AKI, Other>
    from ExtensionParamFrom where type ExtensionParamFrom<AKI, Other> = ord_choice_result!(AKI, Other);
    to ExtensionParamPoly where pub enum ExtensionParamPoly<AKI, Other> {
        AuthorityKeyIdentifier(AKI),
        Other(Other),
    }

    spec SpecExtensionParamValue with <Seq<u8>, Seq<u8>>;
    exec ExtensionParamValue<'a> with <&'a [u8], &'a [u8]>;
    owned ExtensionParamValueOwned with <Vec<u8>, Vec<u8>>;

    forward(x) {
        match x {
            inj_ord_choice_pat!(p, *) => ExtensionParamPoly::AuthorityKeyIdentifier(p),
            inj_ord_choice_pat!(*, p) => ExtensionParamPoly::Other(p),
        }
    }

    backward(y) {
        match y {
            ExtensionParamPoly::AuthorityKeyIdentifier(p) => inj_ord_choice_result!(p, *),
            ExtensionParamPoly::Other(p) => inj_ord_choice_result!(*, p),
        }
    }
}

}
