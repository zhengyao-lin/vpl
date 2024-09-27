use vstd::prelude::*;

use crate::asn1::*;
use crate::asn1::Boolean;

use crate::common::*;

verus! {

// pub type ExtensionParamInner = ord_choice_type!(Cond<ASN1<OctetString>>, Cond<ASN1<OctetString>>);

// wrap_combinator! {
//     pub struct ExtensionParam {
//         pub oid: ObjectIdentifierValue,
//     }: ExtensionParamInner = ord_choice!(
//         Cond { cond: oid.is(&[ 2, 5, 29, 35 ]), inner: ASN1(OctetString) },
//         Cond { cond: !oid.is(&[ 2, 5, 29, 35 ]), inner: ASN1(OctetString) },
//     );
// }

// #[derive(Debug, View)]
// pub struct ExtensionParam {
//     pub oid: ObjectIdentifierValue,
// }

// pub type ExtensionParamInner = ASN1<OctetString>;

// #[derive(Debug, View)]
// pub struct ExtensionParam;

// impl SpecCombinator for ExtensionParam {
//     type SpecResult = <<ExtensionParamInner as View>::V as SpecCombinator>::SpecResult;

//     closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()>;

//     #[verifier::external_body]
//     proof fn spec_parse_wf(&self, s: Seq<u8>) {
//         // $inner_expr.view().spec_parse_wf(s)
//     }

//     closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()>;
// }

// impl SecureSpecCombinator for ExtensionParam {}

// impl Combinator for ExtensionParam {
//     type Result<'a> = <ExtensionParamInner as Combinator>::Result<'a>;
//     type Owned = <ExtensionParamInner as Combinator>::Owned;
//     fn length(&self) -> Option<usize> {
//         let _: ExtensionParamInner = (ASN1(OctetString));
//         (ASN1(OctetString)).length()
//     }
//     fn exec_is_prefix_secure() -> bool {
//         ExtensionParamInner::exec_is_prefix_secure()
//     }
//     fn parse<'a>(&self, s: &'a [u8]) -> Result<(usize, Self::Result<'a>), ParseError> {
//         let res = (ASN1(OctetString)).parse(s);
//         #[cfg(parser_trace)]
//         {
//             use polyfill::*;
//             println_join!("[", stringify!(ExtensionParam), "] ", format_dbg(&res));
//         }
//         res
//     }
//     fn serialize(
//         &self,
//         v: Self::Result<'_>,
//         data: &mut Vec<u8>,
//         pos: usize,
//     ) -> Result<usize, SerializeError> {
//         (ASN1(OctetString)).serialize(v, data, pos)
//     }
// }

}
