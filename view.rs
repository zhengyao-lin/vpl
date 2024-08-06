use vstd::prelude::*;

use crate::proof::*;
use crate::checker::*;

// View impl's from checker::<X> to proof::Spec<X>

verus! {

impl View for FnName {
    type V = SpecFnName;
    open spec fn view(&self) -> Self::V {
        match self {
            FnName::User(name, arity) => SpecFnName::User(name.view(), *arity as int),
            FnName::Eq => SpecFnName::Eq,
            FnName::Not => SpecFnName::Not,
            FnName::Forall => SpecFnName::Forall,
        }
    }
}

impl View for TermX {
    type V = SpecTerm;
    /// TODO: Verus issue #1222
    closed spec fn view(&self) -> Self::V;
}

impl TermX {
    #[verifier::external_body]
    pub broadcast proof fn axiom_view(&self)
        ensures #[trigger] self.view() == match self {
            TermX::Var(v) => SpecTerm::Var(v.view()),
            TermX::App(name, args) => SpecTerm::App(name.view(), args.deep_view()),
        }
    {}
}

impl View for RuleX {
    type V = SpecRule;

    open spec fn view(&self) -> Self::V {
        SpecRule {
            head: self.head.view(),
            body: self.body.deep_view(),
        }
    }
}

impl View for ProgramX {
    type V = SpecProgram;

    open spec fn view(&self) -> Self::V {
        SpecProgram {
            rules: self.rules.deep_view(),
        }
    }
}

impl View for Subst {
    type V = SpecSubst;

    open spec fn view(&self) -> Self::V {
        SpecSubst(self.0.deep_view())
    }
}

impl View for Theorem {
    type V = SpecTheorem;

    open spec fn view(&self) -> Self::V {
        SpecTheorem {
            stmt: self.stmt.view(),
            proof: self.proof.view(),
        }
    }
}

impl DeepView for TermX {
    type V = SpecTerm;

    open spec fn deep_view(&self) -> Self::V {
        self.view()
    }
}

impl DeepView for RuleX {
    type V = SpecRule;

    open spec fn deep_view(&self) -> Self::V {
        self.view()
    }
}

impl DeepView for Theorem {
    type V = SpecTheorem;

    open spec fn deep_view(&self) -> Self::V {
        self.view()
    }
}

}
