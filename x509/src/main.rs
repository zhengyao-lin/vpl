mod asn1;

use der::Encode;

use asn1::*;

fn test_var_int() {
    assert!(VarUInt(0).parse(&[ 1, 2, 3 ]).unwrap() == (0, 0));
    assert!(VarUInt(8).parse(&[ 0xff, 0x8f, 0x28, 0, 0, 0, 0, 0 ]).unwrap() == (8, 0xff8f_2800_0000_0000));
    assert!(VarInt(0).parse(&[ 0x7f ]).unwrap() == (0, 0));
    assert!(VarInt(1).parse(&[ 0xff ]).unwrap() == (1, -1));
    assert!(VarInt(2).parse(&[ 0x7f, 0xff ]).unwrap() == (2, 0x7fff));
    assert!(VarInt(2).parse(&[ 0x80, 0x00 ]).unwrap() == (2, -32768));

    let mut data = vec![0; 8];
    assert!(VarUInt(0).serialize(0, &mut data, 0).unwrap() == 0);
    assert!(data == [0; 8]);

    let mut data = vec![0; 8];
    assert!(VarUInt(2).serialize(0xbeef, &mut data, 0).unwrap() == 2);
    assert!(data == [ 0xbe, 0xef, 0, 0, 0, 0, 0, 0 ]);

    let mut data = vec![0; 8];
    assert!(VarInt(2).serialize(0x7fff, &mut data, 0).unwrap() == 2);
    assert!(data == [ 0x7f, 0xff, 0, 0, 0, 0, 0, 0 ]);

    let mut data = vec![0; 8];
    assert!(VarInt(2).serialize(-1, &mut data, 0).unwrap() == 2);
    assert!(data == [ 0xff, 0xff, 0, 0, 0, 0, 0, 0 ]);

    let mut data = vec![0; 8];
    assert!(VarInt(0).serialize(0, &mut data, 0).unwrap() == 0);
    assert!(data == [ 0, 0, 0, 0, 0, 0, 0, 0 ]);

    let mut data = vec![0; 8];
    assert!(VarUInt(1).serialize(256, &mut data, 0).is_err());
    assert!(VarInt(1).serialize(-1000, &mut data, 0).is_err());
    assert!(VarInt(1).serialize(0x80, &mut data, 0).is_err());
}

fn test_length() {
    assert!(Length.parse(&[ 0x0 ]).unwrap() == (1, 0));
    assert!(Length.parse(&[ 0x7f ]).unwrap() == (1, 0x7f));
    assert!(Length.parse(&[ 0x80 ]).is_err());
    assert!(Length.parse(&[ 0x81, 0x80 ]).unwrap() == (2, 0x80));
    assert!(Length.parse(&[ 0x81, 0x7f ]).is_err());
    assert!(Length.parse(&[ 0x82, 0x00, 0xff ]).is_err());
    assert!(Length.parse(&[ 0x82, 0x0f, 0xff ]).unwrap() == (3, 0x0fff));
}

fn test_asn1_int() {
    assert!(Integer.parse(&[ 0x01, 0x00 ]).unwrap() == (2, 0));
    assert!(Integer.parse(&[ 0x00 ]).is_err());
    assert!(Integer.parse(&[ 0x01, 0xff ]).unwrap() == (2, -1));
    assert!(Integer.parse(&[ 0x81, 0x01, 0xff ]).is_err());
    assert!(Integer.parse(&[ 0x02, 0x00, 0xff ]).unwrap() == (3, 0xff));
    assert!(Integer.parse(&[ 0x02, 0x00, 0x7f ]).is_err()); // violation of minimal encoding
}

fn serialize_int(v: IntegerValue) -> Result<Vec<u8>, ()> {
    let mut data = vec![0; 16];
    data[0] = 0x02; // Prepend the tag byte
    let len = Integer.serialize(v, &mut data, 1)?;
    data.truncate(len + 1);
    Ok(data)
}

/// Compare results of serialize to a common ASN.1 DER library
fn diff_test_int_serialize() {
    let diff = |i| {
        let res1 = serialize_int(i);
        let res2 = i.to_der();
        
        // println!("Testing {}", i);

        match (&res1, &res2) {
            (Ok(v1), Ok(v2)) => assert!(v1 == v2, "Mismatch when encoding {}: {:?} {:?}", i, v1, v2),
            (Err(_), Err(_)) => {},
            _ => panic!("Mismatch when encoding {}: {:?} {:?}", i, &res1, &res2),
        }
    };

    diff(0);
    diff(i64::MAX);
    diff(i64::MIN);

    for i in 0..65535i64 {
        diff(i);
    }

    for i in -65535i64..0 {
        diff(i);
    }
}

fn serialize_octet_string(v: &[u8]) -> Result<Vec<u8>, ()> {
    let mut data = vec![0; v.len() + 10];
    data[0] = 0x04; // Prepend the tag byte
    let len = OctetString.serialize(v, &mut data, 1)?;
    data.truncate(len + 1);
    Ok(data)
}

fn diff_test_octet_string_serialize() {
    let diff = |bytes: &[u8]| {
        let res1 = serialize_octet_string(bytes);
        let res2 = der::asn1::OctetString::new(bytes).unwrap().to_der();
        
        // println!("Testing {:?}: {:?} {:?}", bytes, res1, res2);

        match (&res1, &res2) {
            (Ok(v1), Ok(v2)) => assert!(v1 == v2, "Mismatch when encoding {:?}: {:?} {:?}", bytes, v1, v2),
            (Err(_), Err(_)) => {},
            _ => panic!("Mismatch when encoding {:?}: {:?} {:?}", bytes, &res1, &res2),
        }
    };

    diff(&[]);
    diff(&[ 0 ]);
    diff(&[ 0; 256 ]);
    diff(&[ 0; 257 ]);
    diff(&[ 0; 65536 ]);
}

fn serialize_utf8_string(v: &str) -> Result<Vec<u8>, ()> {
    let mut data = vec![0; v.len() + 10];
    data[0] = 0x0c; // Prepend the tag byte
    let len = UTF8String.serialize(v, &mut data, 1)?;
    data.truncate(len + 1);
    Ok(data)
}

fn diff_test_utf8_string_serialize() {
    let diff = |s: &str| {
        let res1 = serialize_utf8_string(s);
        let res2 = s.to_string().to_der();

        match (&res1, &res2) {
            (Ok(v1), Ok(v2)) => assert!(v1 == v2, "Mismatch when encoding {:?}: {:?} {:?}", s, v1, v2),
            (Err(_), Err(_)) => {},
            _ => panic!("Mismatch when encoding {:?}: {:?} {:?}", s, &res1, &res2),
        }
    };

    diff("");
    diff("asdsad");
    diff("黑风雷");
    diff("👨‍👩‍👧‍👦");
    diff("黑风雷".repeat(256).as_str());
}

fn serialize_bit_string(v: BitStringValue) -> Result<Vec<u8>, ()> {
    let mut data = vec![0; v.bit_string().len() + 10];
    data[0] = 0x03; // Prepend the tag byte
    let len = BitString.serialize(v, &mut data, 1)?;
    data.truncate(len + 1);
    Ok(data)
}

fn diff_test_bit_string_serialize() {
    // The first byte of raw should denote the number of trailing zeros
    let diff = |raw: &[u8]| {
        let res1 = serialize_bit_string(BitStringValue::new_raw(raw).unwrap());
        let res2 = der::asn1::BitString::new(raw[0], &raw[1..]).unwrap().to_der();
        
        // println!("Testing {:?}: {:?} {:?}", raw, res1, res2);

        match (&res1, &res2) {
            (Ok(v1), Ok(v2)) => assert!(v1 == v2, "Mismatch when encoding {:?}: {:?} {:?}", raw, res1, res2),
            (Err(_), Err(_)) => {},
            _ => panic!("Mismatch when encoding {:?}: {:?} {:?}", raw, res1, res2),
        }
    };

    diff(&[0]);
    diff(&[5, 0b11100000]);
    diff(&[4, 0b11100000]);
}

fn serialize_ia5_string(v: &str) -> Result<Vec<u8>, ()> {
    let mut data = vec![0; v.len() + 10];
    data[0] = 0x16; // Prepend the tag byte
    let len = IA5String.serialize(IA5StringValue::new(v.as_bytes()).unwrap(), &mut data, 1)?;
    data.truncate(len + 1);
    Ok(data)
}

fn diff_test_ia5_string_serialize() {
    let diff = |s: &str| {
        let res1 = serialize_ia5_string(s);
        let res2 = der::asn1::Ia5StringRef::new(s).unwrap().to_der();

        // println!("Testing {:?}: {:?} {:?}", s, res1, res2);

        match (&res1, &res2) {
            (Ok(v1), Ok(v2)) => assert!(v1 == v2, "Mismatch when encoding {:?}: {:?} {:?}", s, v1, v2),
            (Err(_), Err(_)) => {},
            _ => panic!("Mismatch when encoding {:?}: {:?} {:?}", s, &res1, &res2),
        }
    };

    diff("");
    diff("\x7f");
    diff("asdsad");
    diff("aaaaaa");
    diff("aaaaa".repeat(100).as_str());
}

fn hexdump(data: &[u8]) {
    for chunk in data.chunks(16) {
        for byte in chunk {
            print!("{:02x} ", byte);
        }
        println!();
    }
}

pub fn main() {
    test_var_int();
    test_length();
    test_asn1_int();
    diff_test_int_serialize();
    diff_test_octet_string_serialize();
    diff_test_utf8_string_serialize();
    diff_test_bit_string_serialize();
    diff_test_ia5_string_serialize();

    hexdump(&der::asn1::ObjectIdentifier::new_unwrap("1.2.0").to_der().unwrap());
}
