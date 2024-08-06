use vstd::prelude::*;
use std::collections::HashMap;

verus! {

#[verifier::ext_equal]
#[verifier::reject_recursive_types(Value)]
pub struct StringHashMap<Value> {
    m: HashMap<String, Value>,
}

impl<Value> View for StringHashMap<Value> {
    type V = Map<Seq<char>, Value>;

    closed spec fn view(&self) -> Self::V;
}

impl<Value> DeepView for StringHashMap<Value> 
    where Value: DeepView
{
    type V = Map<Seq<char>, <Value as DeepView>::V>;

    open spec fn deep_view(&self) -> Self::V {
        self
            .view()
            .map_values(|v: Value| v.deep_view())
    }
}

impl<Value:PartialEq> PartialEq for StringHashMap<Value> {
    fn eq(&self, other :&Self) -> bool{
        self.m == other.m
    } 
}

impl<Value: Clone + DeepView> Clone for StringHashMap<Value> {
    #[verifier::external_body]
    fn clone(&self) -> (res: Self) 
        ensures self.deep_view() == res.deep_view()
    {
        Self { m: self.m.clone() }
    }
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

pub broadcast proof fn axiom_string_hash_map_spec_len<Value>(m: &StringHashMap<Value>)
    ensures
        #[trigger] m.spec_len() == m@.len(),
{
    admit();
}

#[cfg_attr(verus_keep_ghost, verifier::prune_unless_this_module_is_used)]
pub broadcast group group_hash_map_axioms {
    axiom_string_hash_map_spec_len,
}

}

// Rc
// verus! {
//     struct InnerRc<T> {
//         rc_cell: std::cell::UnsafeCell<u64>,
//         t: T,
//     }
    
//     struct Rc<T> {
//         ptr: *mut InnerRc<T>,
//     }
    
//     impl<T> Rc<T> {
//         fn new(t: T) -> Self {
//             // Allocate a new InnerRc object, initialize the counter to 1,
//             // and return a pointer to it.
//             let rc_cell = std::cell::UnsafeCell::new(1);
//             let inner_rc = InnerRc { rc_cell, t };
//             let ptr = Box::leak(Box::new(inner_rc));
//             Rc { ptr }
//         }
    
//         fn clone(&self) -> Self {
//             unsafe {
//                 // Increment the counter.
//                 // If incrementing the counter would lead to overflow, then abort.
//                 let inner_rc = &*self.ptr;
//                 let count = *inner_rc.rc_cell.get();
//                 if count == 0xffffffffffffffff {
//                     std::process::abort();
//                 }
//                 *inner_rc.rc_cell.get() = count + 1;
//             }
    
//             // Return a new Rc object with the same pointer.
//             Rc { ptr: self.ptr }
//         }
    
//         fn drop(self) {
//             unsafe {
//                 // Decrement the counter.
//                 let inner_rc = &*self.ptr;
//                 let count = *inner_rc.rc_cell.get() - 1;
//                 *inner_rc.rc_cell.get() = count;
    
//                 // If the counter hits 0, drop the `T` and deallocate the memory.
//                 if count == 0 {
//                     std::ptr::drop_in_place(&mut (*self.ptr).t);
//                     std::alloc::dealloc(self.ptr as *mut u8, std::alloc::Layout::for_value(&*self.ptr));
//                 }
//             }
//         }
    
//         fn borrow(&self) -> &T {
//             unsafe { &(*self.ptr).t }
//         }
//     }
// }
