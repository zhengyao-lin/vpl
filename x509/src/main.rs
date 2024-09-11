mod vest;
mod polyfill;
mod asn1;

use vest::Combinator;

fn test_var_int() {
    assert!(asn1::VarUInt(0).parse(&[ 1, 2, 3 ]).unwrap() == (0, 0));
    assert!(asn1::VarUInt(8).parse(&[ 0xff, 0x8f, 0x28, 0, 0, 0, 0, 0 ]).unwrap() == (8, 0xff8f_2800_0000_0000));
    assert!(asn1::VarInt(0).parse(&[ 0x7f ]).unwrap() == (0, 0));
    assert!(asn1::VarInt(1).parse(&[ 0xff ]).unwrap() == (1, -1));
    assert!(asn1::VarInt(2).parse(&[ 0x7f, 0xff ]).unwrap() == (2, 0x7fff));
    assert!(asn1::VarInt(2).parse(&[ 0x80, 0x00 ]).unwrap() == (2, -32768));

    let mut data = vec![0; 8];
    assert!(asn1::VarUInt(0).serialize(0, &mut data, 0).unwrap() == 0);
    assert!(data == [0; 8]);

    let mut data = vec![0; 8];
    assert!(asn1::VarUInt(2).serialize(0xbeef, &mut data, 0).unwrap() == 2);
    assert!(data == [ 0xbe, 0xef, 0, 0, 0, 0, 0, 0 ]);

    let mut data = vec![0; 8];
    assert!(asn1::VarInt(2).serialize(0x7fff, &mut data, 0).unwrap() == 2);
    assert!(data == [ 0x7f, 0xff, 0, 0, 0, 0, 0, 0 ]);

    let mut data = vec![0; 8];
    assert!(asn1::VarInt(2).serialize(-1, &mut data, 0).unwrap() == 2);
    assert!(data == [ 0xff, 0xff, 0, 0, 0, 0, 0, 0 ]);

    let mut data = vec![0; 8];
    assert!(asn1::VarInt(0).serialize(0, &mut data, 0).unwrap() == 0);
    assert!(data == [ 0, 0, 0, 0, 0, 0, 0, 0 ]);

    let mut data = vec![0; 8];
    assert!(asn1::VarUInt(1).serialize(256, &mut data, 0).is_err());
    assert!(asn1::VarInt(1).serialize(-1000, &mut data, 0).is_err());
    assert!(asn1::VarInt(1).serialize(0x80, &mut data, 0).is_err());
}

fn test_length() {
    assert!(asn1::Length.parse(&[ 0x0 ]).unwrap() == (1, 0));
    assert!(asn1::Length.parse(&[ 0x7f ]).unwrap() == (1, 0x7f));
    assert!(asn1::Length.parse(&[ 0x80 ]).is_err());
    assert!(asn1::Length.parse(&[ 0x81, 0x80 ]).unwrap() == (2, 0x80));
    assert!(asn1::Length.parse(&[ 0x81, 0x7f ]).is_err());
    assert!(asn1::Length.parse(&[ 0x82, 0x00, 0xff ]).is_err());
    assert!(asn1::Length.parse(&[ 0x82, 0x0f, 0xff ]).unwrap() == (3, 0x0fff));
}

fn test_asn1_int() {
    assert!(asn1::Integer.parse(&[ 0x02, 0x01, 0x00 ]).unwrap() == (3, 0));
    assert!(asn1::Integer.parse(&[ 0x02, 0x00 ]).is_err());
    assert!(asn1::Integer.parse(&[ 0x02, 0x01, 0xff ]).unwrap() == (3, -1));
    assert!(asn1::Integer.parse(&[ 0x02, 0x81, 0x01, 0xff ]).is_err());
    assert!(asn1::Integer.parse(&[ 0x02, 0x02, 0x00, 0xff ]).unwrap() == (4, 0xff));
    assert!(asn1::Integer.parse(&[ 0x02, 0x02, 0x00, 0x7f ]).is_err()); // violation of minimal encoding
}

pub fn main() {
    test_var_int();
    test_length();
    test_asn1_int();
}
