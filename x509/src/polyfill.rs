use vstd::prelude::*;

verus! {
    #[verifier::external_body]
    pub fn slice_drop_first<V>(s: &[V]) -> (res: &[V])
        requires s.len() > 0
        ensures res@ == s@.drop_first()
    {
        &s[1..]
    }
}
