// Impl of Display for some of the X.509 types

use std::fmt::{self, Display};

use crate::asn1::*;
use crate::common::*;
use super::*;

impl<'a> Display for DirectoryStringValue<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            DirectoryStringValue::PrintableString(s) => write!(f, "{}", s),
            DirectoryStringValue::UTF8String(s) => write!(f, "{}", s),
            DirectoryStringValue::IA5String(s) => write!(f, "{}", s),
            DirectoryStringValue::TeletexString(..) => write!(f, "<TeletexString>"),
            DirectoryStringValue::UniversalString(..) => write!(f, "<UniversalString>"),
            DirectoryStringValue::BMPString(..) => write!(f, "<BMPString>"),
        }
    }
}

impl<'a> Display for AttributeTypeAndValueValue<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.typ.polyfill_eq(&oid!(2, 5, 4, 3)) {
            write!(f, "CN={}", self.value)
        } else if self.typ.polyfill_eq(&oid!(2, 5, 4, 6)) {
            write!(f, "C={}", self.value)
        } else if self.typ.polyfill_eq(&oid!(2, 5, 4, 7)) {
            write!(f, "L={}", self.value)
        } else if self.typ.polyfill_eq(&oid!(2, 5, 4, 8)) {
            write!(f, "ST={}", self.value)
        } else if self.typ.polyfill_eq(&oid!(2, 5, 4, 10)) {
            write!(f, "O={}", self.value)
        } else if self.typ.polyfill_eq(&oid!(2, 5, 4, 11)) {
            write!(f, "OU={}", self.value)
        } else if self.typ.polyfill_eq(&oid!(2, 5, 4, 9)) {
            write!(f, "STREET={}", self.value)
        } else if self.typ.polyfill_eq(&oid!(2, 5, 4, 5)) {
            write!(f, "SERIALNUMBER={}", self.value)
        } else if self.typ.polyfill_eq(&oid!(1, 2, 840, 113549, 1, 9, 1)) {
            write!(f, "EMAILADDRESS={}", self.value)
        } else {
            write!(f, "{:?}={}", self.typ, self.value)
        }
    }
}

impl<'a> Display for RDNValue<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (i, attr) in self.0.iter().enumerate() {
            if i == 0 {
                write!(f, "{}", attr)?;
            } else {
                write!(f, " {}", attr)?;
            }
        }
        Ok(())
    }
}

impl<'a> Display for NameValue<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (i, rdn) in self.0.iter().enumerate() {
            if i == 0 {
                write!(f, "{}", rdn)?;
            } else {
                write!(f, ", {}", rdn)?;
            }
        }
        Ok(())
    }
}
