use vstd::prelude::*;
use vpl::*;
use parser::{*, x509::*};

use super::facts::*;
use super::cert::*;

verus! {

broadcast use vpl::lemma_ext_equal_deep;

/// Generate all facts about a chain of certificates
pub struct ChainFacts;

impl ChainFacts {
    /// Generate facts for each certificate from index i, until hit end or None
    pub closed spec fn spec_facts_helper(t: Seq<SpecCertificateValue>, i: int) -> Option<Seq<SpecRule>>
        decreases t.len() - i
    {
        if i >= t.len() {
            Some(seq![])
        } else {
            if_let! {
                let Some(facts) = CertificateFacts::spec_facts(CertIndexed::new(t[i], i as LiteralInt));
                let Some(rest) = Self::spec_facts_helper(t, i + 1);
                Some(facts + rest)
            }
        }
    }
}

impl<'a> Facts<VecDeep<CertificateValue<'a>>> for ChainFacts {
    open spec fn spec_facts(t: Seq<SpecCertificateValue>) -> Option<Seq<SpecRule>>
    {
        Self::spec_facts_helper(t, 0)
    }

    fn facts(t: &VecDeep<CertificateValue<'a>>, out: &mut VecDeep<Rule>) -> (res: Result<(), ValidationError>) {
        let len = t.len();

        if len > LiteralInt::MAX as usize {
            return Err(ValidationError::IntegerOverflow);
        }

        // Generate facts for each certificate
        for i in 0..len
            invariant
                len == t@.len(),
                len <= LiteralInt::MAX,

                Self::spec_facts_helper(t@, i as int) matches Some(rest) ==> {
                    &&& Self::spec_facts_helper(t@, 0) matches Some(full)
                    &&& old(out)@ + full =~= out@ + rest
                }
        {
            CertificateFacts::facts(&CertIndexed::new(t.get(i), i as LiteralInt), out)?;
        }

        Ok(())
    }
}

}
