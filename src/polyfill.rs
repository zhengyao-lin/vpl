use std::fmt::Debug;
use std::fmt::Display;
use std::num::TryFromIntError;
use std::rc::Rc;
use vstd::prelude::*;

use crate::proof::*;

// Verus specs for some std functions

verus! {

#[verifier::external_body]
pub fn str_to_rc_str(s: &str) -> (res: Rc<str>)
    ensures
        s@ == res@,
{
    s.into()
}

#[verifier::external_body]
pub fn rc_str_to_str(s: &Rc<str>) -> (res: &str)
    ensures
        s@ == res@,
{
    s.as_ref()
}

#[verifier::external_body]
pub fn rc_str_eq(s1: &Rc<str>, s2: &Rc<str>) -> (res: bool)
    ensures
        res == (s1@ == s2@),
{
    s1 == s2
}

#[verifier::external_body]
pub fn rc_str_eq_str(s1: &Rc<str>, s2: &str) -> (res: bool)
    ensures
        res == (s1@ == s2@),
{
    s1.as_ref() == s2
}

#[verifier::external_body]
pub fn rc_as_ref<T: View>(rc: &Rc<T>) -> (res: &T)
    ensures
        rc.view() == res.view(),
{
    rc.as_ref()
}

/// By Travis
pub fn vec_map<T, U>(v: &Vec<T>, f: impl Fn(&T) -> U) -> (res: Vec<U>)
    requires
        forall|i| #![trigger v[i]] 0 <= i < v.len() ==> call_requires(f, (&v[i],)),
    ensures
        res.len() == v.len(),
        forall|i|
            #![trigger v[i]]
            0 <= i < v.len() ==> call_ensures(f, (&v[i],), #[trigger] res[i]),
{
    let mut res = Vec::new();
    let mut j = 0;
    while j < v.len()
        invariant
            forall|i| #![trigger v[i]] 0 <= i < v.len() ==> call_requires(f, (&v[i],)),
            0 <= j <= v.len(),
            j == res.len(),
            forall|i| #![trigger v[i]] 0 <= i < j ==> call_ensures(f, (&v[i],), #[trigger] res[i]),
    {
        res.push(f(&v[j]));
        j += 1;
    }
    res
}

#[verifier::external_body]
pub fn vec_set<T>(v: &mut Vec<T>, i: usize, x: T)
    requires
        0 <= i < old(v).len(),
    ensures
        v.len() == old(v).len() && (forall|j| 0 <= j < v.len() && j != i ==> v[j] == old(v)[j])
            && v[i as int] == x,
{
    v[i] = x;
}

/// Copied from Verus example
pub fn vec_reverse<T: DeepView>(v: &mut Vec<&T>)
    ensures
        v.len() == old(v).len(),
        old(v).deep_view().reverse() =~= v.deep_view(),
{
    let length = v.len();
    let ghost v1 = v.deep_view();
    for n in 0..(length / 2)
        invariant
            length == v.len(),
            forall|i: int| #![auto] 0 <= i < n ==> v[i].deep_view() == v1[length - 1 - i],
            forall|i: int| #![auto] 0 <= i < n ==> v1[i] == v[length - 1 - i].deep_view(),
            forall|i: int| n <= i && i + n < length ==> #[trigger] v[i].deep_view() == v1[i],
    {
        let x = v[n];
        let y = v[length - n - 1];
        v.set(n, y);
        v.set(length - n - 1, x);
    }
}

/// Join a list of strings by the separator `sep`
pub fn join_strs(list: &Vec<&str>, sep: &str) -> (res: String)
    ensures
        res@ =~= seq_join(list@.map_values(|v: &str| v.view()), sep@),
{
    let mut res = string_new();
    assert(res@ =~= seq![]);

    let ghost list_deep_view = list@.map_values(|v: &str| v.view());

    for i in 0..list.len()
        invariant
            list_deep_view.len() == list.len(),
            forall|i| #![auto] 0 <= i < list.len() ==> list_deep_view[i] == list[i]@,
            res@ =~= seq_join(list_deep_view.take(i as int), sep@),
    {
        if i != 0 {
            let ghost old_res = res@;
            res.append(sep);
            res.append(list[i]);
            assert(list_deep_view.take((i + 1) as int).drop_last() =~= list_deep_view.take(
                i as int,
            ));
        } else {
            res.append(list[i]);
        }
    }
    assert(list_deep_view.take(list.len() as int) =~= list_deep_view);

    res
}

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExtTryFromIntError(TryFromIntError);

#[verifier::external_body]
pub fn i64_try_into_usize(x: i64) -> (res: Result<usize, TryFromIntError>)
    ensures
        res matches Ok(y) ==> x as int == y as int,
{
    x.try_into()
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

#[verifier::external_body]
pub fn string_new() -> (res: String)
    ensures
        res@ == Seq::<char>::empty(),
{
    String::new()
}

#[verifier::external_body]
pub fn format_dbg(a: impl Debug) -> String {
    format!("{:?}", a)
}

#[verifier::external_body]
pub fn format(a: impl Display) -> String {
    format!("{}", a)
}

#[verifier::external_body]
pub fn join_2(a: impl Display, b: impl Display) -> String {
    format!("{}{}", a, b)
}

/// A temporary replacement for format!
/// join!(a, b, c) is equivalent to format!("{}{}{}", a, b, c)
#[allow(unused_macros)]
#[macro_export]
macro_rules! join {
    ($a:expr) => {format($a)};
    ($a:expr, $($rest:expr),+) => {
        join_2($a, join!($($rest),+))
    };
}

#[allow(unused_imports)]
pub use join;

/// print_join!(a, b, c) is equivalent to print!("{}{}{}", a, b, c)
#[allow(unused_macros)]
#[macro_export]
macro_rules! print_join {
    ($($args:expr),+) => {
        print(join!($($args),+));
    }
}

#[allow(unused_imports)]
pub use print_join;

/// println_join!(a, b, c) is equivalent to println!("{}{}{}", a, b, c)
#[allow(unused_macros)]
#[macro_export]
macro_rules! println_join {
    ($($args:expr),+) => {
        println(join!($($args),+));
    }
}

#[allow(unused_imports)]
pub use println_join;

/// eprint_join!(a, b, c) is equivalent to eprint!("{}{}{}", a, b, c)
#[allow(unused_macros)]
#[macro_export]
macro_rules! eprint_join {
    ($($args:expr),+) => {
        eprint(join!($($args),+));
    }
}

#[allow(unused_imports)]
pub use eprint_join;

/// eprintln_join!(a, b, c) is equivalent to eprintln!("{}{}{}", a, b, c)
#[allow(unused_macros)]
#[macro_export]
macro_rules! eprintln_join {
    ($($args:expr),+) => {
        eprintln(join!($($args),+));
    }
}

#[allow(unused_imports)]
pub use eprintln_join;

} // verus!
