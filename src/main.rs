mod proof;
mod checker;
mod containers;
mod view;
mod polyfill;
mod solver;
mod trace;

use vstd::prelude::*;

verus! {

pub fn main() {
    crate::trace::test();
}

}
