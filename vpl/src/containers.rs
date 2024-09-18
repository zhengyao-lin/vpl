/// Copied from https://github.com/verus-lang/verus/blob/3580369d3b2da8511a1ef451d184a03bf7c30cdb/source/vstd/hash_map.rs
/// for some minor tweaks and to avoid any future changes in Verus.

#[allow(unused_imports)]
use vstd::map::*;
#[allow(unused_imports)]
use vstd::pervasive::*;
use vstd::prelude::*;

#[allow(unused_imports)]
use core::hash::Hash;
use std::collections::HashMap;

verus! {

#[verifier::ext_equal]
#[verifier::reject_recursive_types(Key)]
#[verifier::reject_recursive_types(Value)]
pub struct HashMapWithView<Key, Value> where Key: View + Eq + Hash {
    m: HashMap<Key, Value>,
}

impl<Key, Value> View for HashMapWithView<Key, Value> where Key: View + Eq + Hash {
    type V = Map<<Key as View>::V, Value>;

    closed spec fn view(&self) -> Self::V;
}

impl<Key, Value> HashMapWithView<Key, Value> where Key: View + Eq + Hash {
    #[verifier::external_body]
    pub fn new() -> (result: Self)
        requires
            forall|k1: Key, k2: Key| k1@ == k2@ ==> k1 == k2,
        ensures
            result@ == Map::<<Key as View>::V, Value>::empty(),
    {
        Self { m: HashMap::new() }
    }

    #[verifier::external_body]
    pub fn with_capacity(capacity: usize) -> (result: Self)
        requires
            forall|k1: Key, k2: Key| k1@ == k2@ ==> k1 == k2,
        ensures
            result@ == Map::<<Key as View>::V, Value>::empty(),
    {
        Self { m: HashMap::with_capacity(capacity) }
    }

    #[verifier::external_body]
    pub fn reserve(&mut self, additional: usize)
        ensures
            self@ == old(self)@,
    {
        self.m.reserve(additional);
    }

    pub open spec fn spec_len(&self) -> usize;

    #[verifier::external_body]
    #[verifier::when_used_as_spec(spec_len)]
    pub fn len(&self) -> (result: usize)
        ensures
            result == self@.len(),
    {
        self.m.len()
    }

    #[verifier::external_body]
    pub fn insert(&mut self, k: Key, v: Value)
        ensures
            self@ == old(self)@.insert(k@, v),
    {
        self.m.insert(k, v);
    }

    #[verifier::external_body]
    pub fn remove(&mut self, k: &Key) -> (res: Option<Value>)
        ensures
            res matches Some(v) ==> {
                &&& old(self)@.contains_key(k@)
                &&& old(self)@[k@] == v
                &&& self@ == old(self)@.remove(k@)
            },
            res matches None ==> {
                &&& !old(self)@.contains_key(k@)
                &&& self@ == old(self)@
            }
    {
        self.m.remove(k)
    }

    #[verifier::external_body]
    pub fn contains_key(&self, k: &Key) -> (result: bool)
        ensures
            result == self@.contains_key(k@),
    {
        self.m.contains_key(k)
    }

    #[verifier::external_body]
    pub fn get<'a>(&'a self, k: &Key) -> (result: Option<&'a Value>)
        ensures
            match result {
                Some(v) => self@.contains_key(k@) && *v == self@[k@],
                None => !self@.contains_key(k@),
            },
    {
        self.m.get(k)
    }

    #[verifier::external_body]
    pub fn clear(&mut self)
        ensures
            self@ == Map::<<Key as View>::V, Value>::empty(),
    {
        self.m.clear()
    }
}

pub broadcast proof fn axiom_hash_map_with_view_spec_len<Key, Value>(
    m: &HashMapWithView<Key, Value>,
) where Key: View + Eq + Hash
    ensures
        #[trigger] m.spec_len() == m@.len(),
{
    admit();
}

#[verifier::ext_equal]
#[verifier::reject_recursive_types(Value)]
#[derive(Debug)]
pub struct StringHashMap<Value> {
    pub m: HashMap<String, Value>,
}

impl<Value> View for StringHashMap<Value> {
    type V = Map<Seq<char>, Value>;

    closed spec fn view(&self) -> Self::V;
}

impl<Value> StringHashMap<Value> {
    #[verifier::external_body]
    pub fn new() -> (result: Self)
        ensures
            result@ == Map::<Seq<char>, Value>::empty(),
    {
        Self { m: HashMap::new() }
    }

    #[verifier::external_body]
    pub fn with_capacity(capacity: usize) -> (result: Self)
        ensures
            result@ == Map::<Seq<char>, Value>::empty(),
    {
        Self { m: HashMap::with_capacity(capacity) }
    }

    #[verifier::external_body]
    pub fn reserve(&mut self, additional: usize)
        ensures
            self@ == old(self)@,
    {
        self.m.reserve(additional);
    }

    pub open spec fn spec_len(&self) -> usize;

    #[verifier::external_body]
    #[verifier::when_used_as_spec(spec_len)]
    pub fn len(&self) -> (result: usize)
        ensures
            result == self@.len(),
    {
        self.m.len()
    }

    #[verifier::external_body]
    pub fn insert(&mut self, k: String, v: Value)
        ensures
            self@ == old(self)@.insert(k@, v),
    {
        self.m.insert(k, v);
    }

    #[verifier::external_body]
    pub fn remove(&mut self, k: &str)
        ensures
            self@ == old(self)@.remove(k@),
    {
        self.m.remove(k);
    }

    #[verifier::external_body]
    pub fn contains_key(&self, k: &str) -> (result: bool)
        ensures
            result == self@.contains_key(k@),
    {
        self.m.contains_key(k)
    }

    #[verifier::external_body]
    pub fn get<'a>(&'a self, k: &str) -> (result: Option<&'a Value>)
        ensures
            match result {
                Some(v) => self@.contains_key(k@) && *v == self@[k@],
                None => !self@.contains_key(k@),
            },
    {
        self.m.get(k)
    }

    #[verifier::external_body]
    pub fn clear(&mut self)
        ensures
            self@ == Map::<Seq<char>, Value>::empty(),
    {
        self.m.clear()
    }
}

impl<Value> DeepView for StringHashMap<Value> where Value: DeepView {
    type V = Map<Seq<char>, <Value as DeepView>::V>;

    open spec fn deep_view(&self) -> Self::V {
        self.view().map_values(|v: Value| v.deep_view())
    }
}

impl<Value: Clone + DeepView> Clone for StringHashMap<Value> {
    #[verifier::external_body]
    fn clone(&self) -> (res: Self)
        ensures
            self.deep_view() == res.deep_view(),
    {
        Self { m: self.m.clone() }
    }
}

pub broadcast proof fn axiom_string_hash_map_spec_len<Value>(m: &StringHashMap<Value>)
    ensures
        #[trigger] m.spec_len() == m@.len(),
{
    admit();
}

pub broadcast group group_hash_map_axioms {
    axiom_hash_map_with_view_spec_len,
    axiom_string_hash_map_spec_len,
}

} // verus!
