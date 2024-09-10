mod vest;
mod vint;

use vest::Combinator;

pub fn main() {
    let (len, res) = vint::VarUInt(8).parse(&[ 0xff, 0x8f, 0x28, 0, 0, 0, 0, 0 ]).unwrap();
    println!("len: {}, res: {:?}", len, res);

    let (len, res) = vint::VarInt(1).parse(&[ 0xff ]).unwrap();
    println!("len: {}, res: {:?}", len, res);
}
