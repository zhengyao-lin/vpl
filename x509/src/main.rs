mod vest;
mod vint;
mod depend;
mod constant;
mod polyfill;
mod asn1;

// use vstd::prelude::*;
// use crate::vest::*;
// use crate::vint::*;
// use crate::constant::*;

use vest::Combinator;

// verus! {
//     fn test_int() {
//         let ghost spec_snd = |l| {
//             Bytes(l as usize)
//         };

//         let test = Depend {
//             fst: U8,
//             snd: (|l| -> (o: Combinator<Result<'a> = u64, Owned = u64, V = u64>)
//                 ensures
//                     o@ == spec_snd(l@),
//                 {
//                     if l < 0x80 {
//                         Const(l as u64)
//                     } else {
//                         VarUInt((l - 0x80u8).into())
//                     }
//                 }),
//             spec_snd: Ghost(spec_snd),
//         };
//     }
// }

fn test_var_int() {
    assert!(vint::VarUInt(0).parse(&[ 1, 2, 3 ]).unwrap() == (0, 0));
    assert!(vint::VarUInt(8).parse(&[ 0xff, 0x8f, 0x28, 0, 0, 0, 0, 0 ]).unwrap() == (8, 0xff8f_2800_0000_0000));
    assert!(vint::VarInt(0).parse(&[ 0x7f ]).unwrap() == (0, 0));
    assert!(vint::VarInt(1).parse(&[ 0xff ]).unwrap() == (1, -1));
    assert!(vint::VarInt(2).parse(&[ 0x7f, 0xff ]).unwrap() == (2, 0x7fff));
    assert!(vint::VarInt(2).parse(&[ 0x80, 0x00 ]).unwrap() == (2, -32768));

    let mut data = vec![0; 8];
    assert!(vint::VarUInt(0).serialize(0, &mut data, 0).unwrap() == 0);
    assert!(data == [0; 8]);

    let mut data = vec![0; 8];
    assert!(vint::VarUInt(2).serialize(0xbeef, &mut data, 0).unwrap() == 2);
    assert!(data == [ 0xbe, 0xef, 0, 0, 0, 0, 0, 0 ]);

    let mut data = vec![0; 8];
    assert!(vint::VarInt(2).serialize(0x7fff, &mut data, 0).unwrap() == 2);
    assert!(data == [ 0x7f, 0xff, 0, 0, 0, 0, 0, 0 ]);

    let mut data = vec![0; 8];
    assert!(vint::VarInt(2).serialize(-1, &mut data, 0).unwrap() == 2);
    assert!(data == [ 0xff, 0xff, 0, 0, 0, 0, 0, 0 ]);

    let mut data = vec![0; 8];
    assert!(vint::VarInt(0).serialize(0, &mut data, 0).unwrap() == 0);
    assert!(data == [ 0, 0, 0, 0, 0, 0, 0, 0 ]);

    let mut data = vec![0; 8];
    assert!(vint::VarUInt(1).serialize(256, &mut data, 0).is_err());
    assert!(vint::VarInt(1).serialize(-1000, &mut data, 0).is_err());
    assert!(vint::VarInt(1).serialize(0x80, &mut data, 0).is_err());
}

pub fn main() {
    test_var_int();
}
