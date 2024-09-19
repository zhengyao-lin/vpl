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

/// A wrapper for Vec with its View implemented
/// one layer deeper than the original Vec
///
/// Otherwise inherits all methods from Vec
#[derive(Debug)]
pub struct VecDeep<T>(pub Vec<T>);

impl<T: View> View for VecDeep<T> {
    type V = Seq<T::V>;

    open spec fn view(&self) -> Self::V {
        vec_deep_view(&self.0)
    }
}

/// Cloning VecDeep clones each element
impl<T: PolyfillClone> PolyfillClone for VecDeep<T> where
{
    /// Same as clone of Vec, but this is a "deep" copy
    fn clone(&self) -> Self {
        VecDeep(clone_vec_inner(&self.0))
    }
}

impl<T: View> VecDeep<T> {
    pub fn new() -> (res: Self)
        ensures
            res@ =~= Seq::<T::V>::empty(),
    {
        VecDeep(Vec::new())
    }

    pub fn push(&mut self, value: T)
        ensures
            self@ =~= old(self)@.push(value@)
    {
        self.0.push(value);
    }

    pub fn len(&self) -> (res: usize)
        ensures
            res == self@.len()
    {
        self.0.len()
    }

    pub fn get(&self, i: usize) -> (res: &T)
        requires
            i < self@.len(),
        ensures
            res@ == self@[i as int],
    {
        &self.0[i]
    }

    pub fn remove(&mut self, i: usize) -> (res: T)
        requires
            i < old(self)@.len(),
        ensures
            res@ =~= old(self)@[i as int],
            self@ =~= old(self)@.remove(i as int),
    {
        self.0.remove(i)
    }

    pub fn append(&mut self, other: &mut VecDeep<T>)
        ensures
            self@ =~= old(self)@ + old(other)@,
            other@ =~= Seq::<T::V>::empty(),
    {
        self.0.append(&mut other.0);
    }

    pub fn split_off(&mut self, at: usize) -> (res: VecDeep<T>)
        requires
            at <= old(self)@.len(),
        ensures
            self@ =~= old(self)@.subrange(0, at as int),
            res@ =~= old(self)@.subrange(at as int, old(self)@.len() as int),
    {
        VecDeep(self.0.split_off(at))
    }

    pub fn from_vec(v: Vec<T>) -> (res: Self)
        ensures
            res@ =~= vec_deep_view(&v),
    {
        VecDeep(v)
    }

    pub fn to_vec(self) -> (res: Vec<T>)
        ensures
            self@ =~= vec_deep_view(&res),
    {
        self.0
    }
}

pub open spec fn vec_deep_view<T: View>(v: &Vec<T>) -> Seq<T::V>
{
    Seq::new(v.len() as nat, |i: int| v@[i]@)
}

/// Clone each element of Vec
pub fn clone_vec_inner<T: PolyfillClone>(v: &Vec<T>) -> (res: Vec<T>)
    ensures vec_deep_view(&res) =~= vec_deep_view(v)
{
    let mut cloned: Vec<T> = Vec::new();

    for i in 0..v.len()
        invariant
            cloned.len() == i,
            forall |j| 0 <= j < i ==> cloned[j]@ == #[trigger] v[j]@,
    {
        cloned.push(v[i].clone());
    }

    cloned
}

}
