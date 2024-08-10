use vstd::prelude::*;
use std::rc::Rc;
use std::fmt::Display;
use std::fmt::Debug;

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
pub fn rc_str_eq_str(s1: &Rc<str>, s2: &str) -> (res: bool)
    ensures res == (s1@ == s2@)
{
    s1.as_ref() == s2
}

#[verifier::external_body]
pub fn rc_as_ref<T: View>(rc: &Rc<T>) -> (res: &T)
    ensures rc.view() == res.view()
{
    rc.as_ref()
}

#[verifier::external_body]
pub fn str_to_lowercase(s: &str) -> String
{
    s.to_lowercase()
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

#[verifier::external_body]
pub fn vec_set<T>(v: &mut Vec<T>, i: usize, x: T)
    requires 0 <= i < old(v).len()
    ensures
        v.len() == old(v).len() &&
        (forall |j| 0 <= j < v.len() && j != i ==> v[j] == old(v)[j]) &&
        v[i as int] == x
{
    v[i] = x;
}

// TODO: can we support println! in verus code?

#[verifier::external_trait_specification]
pub trait ExtDisplay {
    type ExternalTraitSpecificationFor: Display;
}

#[verifier::external_body]
pub fn print<T: Display>(s: T) {
    print!("{}", s);
}

#[verifier::external_body]
pub fn println<T: Display>(s: T) {
    println!("{}", s);
}

#[verifier::external_body]
pub fn print_debug<T: Debug>(s: T) {
    print!("{:?}", s);
}

#[verifier::external_body]
pub fn println_debug<T: Debug>(s: T) {
    println!("{:?}", s);
}

#[verifier::external_body]
pub fn eprint<T: Display>(s: T) {
    eprint!("{}", s);
}

#[verifier::external_body]
pub fn eprintln<T: Display>(s: T) {
    eprintln!("{}", s);
}

#[verifier::external_body]
pub fn eprint_debug<T: Debug>(s: T) {
    eprint!("{:?}", s);
}

#[verifier::external_body]
pub fn eprintln_debug<T: Debug>(s: T) {
    eprintln!("{:?}", s);
}

}
