use vstd::prelude::*;

verus! {
    /// TODO: this might not be sound
    #[verifier::external_body]
    pub fn eq<V: Eq>(a: &V, b: &V) -> (res: bool)
        ensures res <==> a == b
    {
        a == b
    }
}
