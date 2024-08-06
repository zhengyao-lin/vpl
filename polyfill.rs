use vstd::prelude::*;
use std::rc::Rc;

// Verus specs for some std functions

verus! {

#[verifier::external_body]
pub fn str_to_rc_str(s: &str) -> (res: Rc<str>)
    ensures s@ == res@
{
    s.into()
}

#[verifier::external_body]
pub fn rc_str_to_str(s: &Rc<str>) -> (res: &str)
    ensures s@ == res@
{
    s.as_ref()
}

#[verifier::external_body]
pub fn rc_str_eq(s1: &Rc<str>, s2: &Rc<str>) -> (res: bool)
    ensures res == (s1@ == s2@)
{
    s1 == s2
}

#[verifier::external_body]
pub fn rc_as_ref<T: View>(rc: &Rc<T>) -> (res: &T)
    ensures rc.view() == res.view()
{
    rc.as_ref()
}

/// By Travis
pub fn vec_map<T, U>(v: &Vec<T>, f: impl Fn(&T) -> U) -> (res: Vec<U>)
    requires
        forall |i| #![trigger v[i]] 0 <= i < v.len() ==> call_requires(f, (&v[i],)),
    ensures
        res.len() == v.len(),
        forall |i| #![trigger v[i]] 0 <= i < v.len() ==> call_ensures(f, (&v[i],), #[trigger] res[i])
{
    let mut res = Vec::new();
    let mut j = 0;
    while j < v.len()
        invariant 
            forall |i| #![trigger v[i]] 0 <= i < v.len() ==> call_requires(f, (&v[i],)),
            0 <= j <= v.len(),
            j == res.len(),
            forall |i| #![trigger v[i]] 0 <= i < j ==> call_ensures(f, (&v[i],), #[trigger] res[i]),
    {
        res.push(f(&v[j]));
        j += 1;
    }
    res
}

}
