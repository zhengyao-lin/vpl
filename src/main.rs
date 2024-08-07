mod proof;
mod checker;
mod containers;
mod view;
mod polyfill;
mod solver;

use vstd::prelude::*;

use crate::solver::test;

verus! {

pub fn main() {
    test();
}

}
