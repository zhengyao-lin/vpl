mod proof;
mod checker;
mod containers;
mod view;
mod polyfill;
mod solver;
mod trace;
mod display;
mod parser;

// use vstd::prelude::*;

// verus! {

pub fn main() {
    crate::parser::test();
}

// }
