use vstd::prelude::*;

use crate::common::*;
use super::tag::*;

verus! {

#[derive(Debug, View, PolyfillClone)]
pub enum GeneralizedTimeZone {
    UTC,
    Local,
    UTCPlus(u8, u8),
    UTCMinus(u8, u8),
}

#[derive(Debug, View, PolyfillClone)]
pub struct GeneralizedTime {
    pub year: u16,
    pub month: u8,
    pub day: u8,
    pub hour: u8,
    pub minute: OptionDeep<u8>,
    pub second: OptionDeep<u8>,
    pub fraction: OptionDeep<u16>,
    pub time_zone: GeneralizedTimeZone,
}

}
