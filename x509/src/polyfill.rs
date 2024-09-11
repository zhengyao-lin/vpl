use vstd::prelude::*;

verus! {
    /// TODO: this might not be sound
    #[verifier::external_body]
    pub fn eq<V: Eq>(a: &V, b: &V) -> (res: bool)
        ensures res <==> a == b
    {
        a == b
    }

    #[verifier::external_body]
    pub fn slice_drop_first<V>(s: &[V]) -> (res: &[V])
        requires s.len() > 0
        ensures res@ == s@.drop_first()
    {
        &s[1..]
    }
}
