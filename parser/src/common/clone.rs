/// Define and implement a temporary Clone replacement "PolyfillClone" for some types

use vstd::prelude::*;

use super::*;

verus! {

/// A temporary replacement Clone
pub trait PolyfillClone: View + Sized {
    fn clone(&self) -> (res: Self)
        ensures
            res@ == self@;
}

impl PolyfillClone for bool {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a> PolyfillClone for &'a str {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, T> PolyfillClone for &'a [T] {
    fn clone(&self) -> Self {
        *self
    }
}

impl PolyfillClone for usize {
    fn clone(&self) -> Self {
        *self
    }
}

// Can't do this due to https://github.com/verus-lang/verus/issues/1108
// impl PolyfillClone for () {
//     fn clone(&self) -> Self {
//         ()
//     }
// }

impl<T: Copy> PolyfillClone for Vec<T>
{
    fn clone(&self) -> Self {
        let mut cloned: Vec<T> = Vec::new();

        for i in 0..self.len()
            invariant
                cloned.len() == i,
                forall |j| 0 <= j < i ==> #[trigger] cloned[j] == self[j],
        {
            cloned.push(self[i]);
        }

        assert(cloned@ =~= self@);

        cloned
    }
}

impl<T1: PolyfillClone, T2: PolyfillClone> PolyfillClone for (T1, T2) {
    fn clone(&self) -> Self {
        (self.0.clone(), self.1.clone())
    }
}

impl<T1: PolyfillClone, T2: PolyfillClone> PolyfillClone for Either<T1, T2> {
    fn clone(&self) -> Self {
        match self {
            Either::Left(v) => Either::Left(v.clone()),
            Either::Right(v) => Either::Right(v.clone()),
        }
    }
}

}
