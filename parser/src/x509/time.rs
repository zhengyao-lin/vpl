use vstd::prelude::*;

use crate::asn1::*;
use crate::common::*;

verus! {

/// In X.509:
/// Time ::= CHOICE {
///     utcTime        UTCTime, // more common
///     generalTime    GeneralizedTime
/// }
///
/// TODO: The restrictions on UTCTime and GeneralizedTime are somewhat complicated,
/// so we use UTF8String as their placeholder for now
pub type TimeInner = Mapped<OrdChoice<ASN1<ImplicitTag<UTF8String>>, ASN1<ImplicitTag<UTF8String>>>, TimeMapper>;

wrap_combinator! {
    pub struct Time: TimeInner =>
        spec SpecTimeValue,
        exec<'a> TimeValue<'a>,
        owned TimeValueOwned,
    =
        Mapped {
            inner: OrdChoice(
                ASN1(ImplicitTag(tag_of!(UTC_TIME), UTF8String)),
                ASN1(ImplicitTag(tag_of!(GENERALIZED_TIME), UTF8String)),
            ),
            mapper: TimeMapper,
        };
}

mapper! {
    pub struct TimeMapper;

    for <UT, GT>
    from TimeFrom where type TimeFrom<UT, GT> = Either<UT, GT>;
    to TimePoly where pub enum TimePoly<UT, GT> {
        UTCTime(UT),
        GeneralizedTime(GT),
    }

    spec SpecTimeValue with <SpecUTF8StringValue, SpecUTF8StringValue>;
    exec TimeValue<'a> with <UTF8StringValue<'a>, UTF8StringValue<'a>>;
    owned TimeValueOwned with <UTF8StringValueOwned, UTF8StringValueOwned>;

    forward(x) {
        match x {
            Either::Left(s) => TimePoly::UTCTime(s),
            Either::Right(s) => TimePoly::GeneralizedTime(s),
        }
    }

    backward(y) {
        match y {
            TimePoly::UTCTime(s) => Either::Left(s),
            TimePoly::GeneralizedTime(s) => Either::Right(s),
        }
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
            let _ = Time.parse(&[]);
        }
    }

    #[test]
    fn sanity() {
        assert!(Time.parse(&[
            0x17, 0x0D, 0x31, 0x36, 0x30, 0x32, 0x30, 0x34, 0x31, 0x32, 0x33, 0x32, 0x32, 0x33, 0x5A,
        ]).is_ok());
    }
}
