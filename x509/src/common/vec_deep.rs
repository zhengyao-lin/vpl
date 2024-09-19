use vstd::prelude::*;
use super::clone::*;

verus! {

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

}
