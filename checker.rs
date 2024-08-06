use vstd::prelude::*;
use std::rc::Rc;

use crate::containers::StringHashMap;
use crate::proof::*;
use crate::polyfill::*;

// A dynamic builder of proofs

verus! {

broadcast use TermX::axiom_view, SpecTerm::axiom_subst;

pub type Var = Rc<str>;
pub type UserFnName = Rc<str>;
pub type RuleId = usize;
pub type Arity = usize;

pub enum FnName {
    // User-defined symbol: (name, arity)
    User(UserFnName, Arity),
    Eq,
    Not,
    Forall,
}

pub type Term = Rc<TermX>;
pub enum TermX {
    Var(Var),
    App(FnName, Vec<Term>),
}

pub type Rule = Rc<RuleX>;
pub struct RuleX {
    pub head: Term,
    pub body: Vec<Term>,
}

pub type Program = Rc<ProgramX>;
pub struct ProgramX {
    pub rules: Vec<Rule>,
}

pub struct Subst(pub StringHashMap<Term>);

pub struct Theorem {
    pub stmt: Term,
    pub proof: Ghost<SpecProof>,
}

impl FnName {
    fn eq(&self, other: &Self) -> (res: bool)
        ensures res == (self@ == other@)
    {
        match (self, other) {
            (FnName::User(name1, arity1), FnName::User(name2, arity2)) =>
                rc_str_eq(name1, name2) && arity1 == arity2,
            (FnName::Eq, FnName::Eq) => true,
            (FnName::Not, FnName::Not) => true,
            (FnName::Forall, FnName::Forall) => true,
            _ => false,
        }
    }
}

impl Clone for FnName {
    fn clone(&self) -> (res: Self)
        ensures self@ == res@
    {
        match self {
            FnName::User(name, arity) => FnName::User(name.clone(), *arity),
            FnName::Eq => FnName::Eq,
            FnName::Not => FnName::Not,
            FnName::Forall => FnName::Forall,
        }
    }
}

impl TermX {
    pub fn var(v: &Var) -> (res: Term)
        ensures res@ == SpecTerm::Var(v@)
    {
        Rc::new(TermX::Var(v.clone()))
    }

    pub fn app(name: &FnName, args: Vec<Term>) -> (res: Term)
        ensures res@ == SpecTerm::App(name@, args.deep_view())
    {
        Rc::new(TermX::App(name.clone(), args))
    }

    /// Apply substitution to a term
    pub fn subst(term: &Term, subst: &Subst) -> (res: Term)
        ensures res@ == term@.subst(subst@)
    {
        match rc_as_ref(term) {
            TermX::Var(v) =>
                if let Some(k) = subst.0.get(v) {
                    k.clone()
                } else {
                    term.clone()
                },

            TermX::App(name, args) => {
                // Apply substitution to each argument
                let subst_args = vec_map(args, |arg| -> (res: Term)
                    ensures res@ == arg@.subst(subst@)
                    { TermX::subst(arg, subst) });
                
                assert(subst_args.deep_view() =~= args.deep_view().map_values(|arg: SpecTerm| arg.subst(subst@)));
                TermX::app(name, subst_args)
            }
        }
    }
}

impl TermX {
    fn eq(&self, other: &Self) -> (res: bool)
        ensures res == (self@ == other@)
    {
        match (self, other) {
            (TermX::Var(v1), TermX::Var(v2)) => rc_str_eq(v1, v2),
            (TermX::App(f1, args1), TermX::App(f2, args2)) => {
                if !f1.eq(f2) {
                    return false;
                }
                
                if args1.len() != args2.len() {
                    assert(self@->App_1 !~= other@->App_1);
                    return false;
                }

                for i in 0..args1.len()
                    invariant
                        0 <= i <= args1.len() &&
                        args1.len() == args2.len() &&
                        args1.deep_view() =~= self@->App_1 &&
                        args2.deep_view() =~= other@->App_1 &&
                        (forall |j: int| 0 <= j < i ==> (#[trigger] args1[j as int])@ == args2[j as int]@)
                {
                    assert(args1[i as int]@ == self@->App_1[i as int]);
                    if !(&args1[i]).eq(&args2[i]) {
                        return false;
                    }
                }

                assert(self@->App_1 =~= other@->App_1);
                true
            }
            _ => false,
        }
    }
}

impl Theorem {
    /// A theorem has the invariant that the ghost proof object is
    /// a valid proof for the statement
    pub open spec fn inv(self, program: SpecProgram) -> bool {
        self@.wf(program)
    }

    /// Axiom SpecProof::ApplyRule
    pub fn apply_rule(program: &Program, rule_idx: RuleId, subst: &Subst, subproofs: Vec<Theorem>) -> (res: Option<Theorem>)
        requires
            0 <= rule_idx < program.rules.len() &&
            forall |i| 0 <= i < subproofs.len() ==> (#[trigger] subproofs[i]).inv(program@)

        ensures
            res matches Some(thm) ==> thm.inv(program@)
    {
        let rule = &program.rules[rule_idx];
        let conclusion = TermX::subst(&rule.head, subst);

        if rule.body.len() != subproofs.len() {
            return None;
        }

        // Check that each subproof matches the corresponding body term (after substitution)
        for i in 0..rule.body.len()
            invariant
                0 <= i <= rule.body.len() &&
                rule.body.len() == subproofs.len() &&
                forall |j| 0 <= j < i ==> (#[trigger] rule.body[j])@.subst(subst@) == subproofs[j].stmt@
        {
            let obligation = &TermX::subst(&rule.body[i], subst);
            if !obligation.eq(&subproofs[i].stmt) {
                return None;
            }
        }

        // Construct the final proof object
        Some(Theorem {
            stmt: conclusion,
            proof: Ghost(SpecProof::ApplyRule {
                rule_idx: rule_idx as int,
                subst: subst@,
                subproofs: subproofs.deep_view(),
            }),
        })
    }

    /// Check that two terms are equal and apply axiom SpecProof::Refl
    pub fn refl(program: &Program, left: &Term, right: &Term) -> (res: Option<Theorem>)
        ensures
            res matches Some(thm) ==> thm.inv(program@)
    {
        if !left.eq(right) {
            return None;
        }

        Some(Theorem {
            stmt: Rc::new(TermX::App(FnName::Eq, vec![left.clone(), right.clone()])),
            proof: Ghost(SpecProof::Refl),
        })
    }
}

}
