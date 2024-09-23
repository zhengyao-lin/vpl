use vstd::prelude::*;

use crate::asn1::*;
use crate::common::*;

verus! {

/// In X.509:
/// AlgorithmIdentifier  ::=  SEQUENCE  {
///     algorithm               OBJECT IDENTIFIER,
///     parameters              ANY DEFINED BY algorithm OPTIONAL
/// }
///
/// TODO: right now parameters are parsed as a byte sequence
pub type AlgorithmIdentifierInner = Mapped<LengthWrapped<(ASN1<ObjectIdentifier>, Tail)>, AlgorithmIdentifierMapper>;

wrap_combinator! {
    struct AlgorithmIdentifier: AlgorithmIdentifierInner =>
        spec SpecAlgorithmIdentifierValue,
        exec<'a> AlgorithmIdentifierValue<'a>,
        owned AlgorithmIdentifierValueOwned,
    = Mapped {
            inner: LengthWrapped((ASN1(ObjectIdentifier), Tail)),
            mapper: AlgorithmIdentifierMapper,
        };
}

asn1_tagged!(AlgorithmIdentifier, TagValue {
    class: TagClass::Universal,
    form: TagForm::Constructed,
    num: 0x10,
});

mapper! {
    struct AlgorithmIdentifierMapper;

    for <Alg, Params>
    from AlgorithmIdentifierFrom where type AlgorithmIdentifierFrom<Alg, Params> = (Alg, Params);
    to AlgorithmIdentifierPoly where pub struct AlgorithmIdentifierPoly<Alg, Params> {
        pub alg: Alg,
        pub params: Params,
    }

    spec SpecAlgorithmIdentifierValue with <SpecObjectIdentifierValue, Seq<u8>>
    exec AlgorithmIdentifierValue<'a> with <ObjectIdentifierValue, &'a [u8]>
    owned AlgorithmIdentifierValueOwned with <ObjectIdentifierValueOwned, Vec<u8>>

    forward(x) {
        AlgorithmIdentifierPoly {
            alg: x.0,
            params: x.1,
        }
    }

    backward(y) {
        (y.alg, y.params)
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
            let _ = ASN1(AlgorithmIdentifier).parse(&[]);
        }
    }

    #[test]
    fn sanity() {
        assert!(ASN1(AlgorithmIdentifier).parse(&[
            0x30, 0x0D, 0x06, 0x09, 0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D, 0x01, 0x01, 0x0C, 0x05, 0x00,
        ]).is_ok());
    }
}
