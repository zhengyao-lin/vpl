mod proof;
mod checker;
mod containers;
mod view;
mod polyfill;
mod solver;
mod trace;
mod display;

use vstd::prelude::*;

verus! {

pub fn main() {
    crate::trace::test();
}

}
