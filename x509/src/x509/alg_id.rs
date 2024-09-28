use vstd::prelude::*;

use crate::asn1::*;
use crate::common::*;

use super::macros::*;

verus! {

// In X.509:
// AlgorithmIdentifier  ::=  SEQUENCE  {
//     algorithm               OBJECT IDENTIFIER,
//     parameters              ANY DEFINED BY algorithm OPTIONAL
// }
//
// TODO: right now parameters are parsed as a byte sequence
asn1_sequence! {
    seq AlgorithmIdentifier {
        alg: ASN1<ObjectIdentifier> = ASN1(ObjectIdentifier),
        #[tail] params: Tail = Tail,
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
