use vstd::prelude::*;

use crate::asn1::*;
use crate::common::*;

use super::time::*;

verus! {

/// In X.509:
/// Validity ::= SEQUENCE {
///     notBefore      Time,
///     notAfter       Time,
/// }
pub type ValidityInner = Mapped<LengthWrapped<(Time, Time)>, ValidityMapper>;

wrap_combinator! {
    struct Validity: ValidityInner =>
        spec SpecValidityValue,
        exec<'a> ValidityValue<'a>,
        owned ValidityValueOwned,
    =
        Mapped {
            inner: LengthWrapped((Time, Time)),
            mapper: ValidityMapper,
        };
}

asn1_tagged!(Validity, TagValue {
    class: TagClass::Universal,
    form: TagForm::Constructed,
    num: 0x10,
});

mapper! {
    struct ValidityMapper;

    for <NA, NB>
    from ValidityFrom where type ValidityFrom<NA, NB> = (NB, NA);
    to ValidityPoly where pub struct ValidityPoly<NA, NB> {
        pub not_before: NB,
        pub not_after: NA,
    }

    spec SpecValidityValue with <SpecTimeValue, SpecTimeValue>
    exec ValidityValue<'a> with <TimeValue<'a>, TimeValue<'a>>
    owned ValidityValueOwned with <TimeValueOwned, TimeValueOwned>

    forward(x) {
        ValidityPoly {
            not_before: x.0,
            not_after: x.1,
        }
    }

    backward(y) {
        (y.not_before, y.not_after)
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
            let _ = ASN1(Validity).parse(&[]);
        }
    }

    #[test]
    fn sanity() {
        assert!(ASN1(Validity).parse(&[
            0x30, 0x1E, 0x17, 0x0D, 0x31, 0x36, 0x30, 0x32, 0x30, 0x34, 0x31, 0x32, 0x33, 0x32, 0x32, 0x33, 0x5A, 0x17, 0x0D, 0x33, 0x34, 0x31, 0x32, 0x33, 0x31, 0x31, 0x37, 0x32, 0x36, 0x33, 0x39, 0x5A,
        ]).is_ok());
    }
}
