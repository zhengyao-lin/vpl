use vstd::prelude::*;
use std::rc::Rc;

use crate::containers::StringHashMap;
use crate::proof::*;
use crate::polyfill::*;

// A dynamic builder of proofs with verified checks

verus! {

broadcast use TermX::axiom_view, SpecTerm::axiom_subst;

pub type Var = Rc<str>;
pub type UserFnName = Rc<str>;
pub type RuleId = usize;
pub type Arity = usize;

#[derive(Debug)]
pub enum FnName {
    // User-defined symbol: (name, arity)
    User(UserFnName, Arity),
    Eq,
    Not,
    Forall,
}

pub type Term = Rc<TermX>;
#[derive(Debug)]
pub enum TermX {
    Var(Var),
    App(FnName, Vec<Term>),
}

pub type Rule = Rc<RuleX>;
#[derive(Debug)]
pub struct RuleX {
    pub head: Term,
    pub body: Vec<Term>,
}

pub type Program = Rc<ProgramX>;
#[derive(Debug)]
pub struct ProgramX {
    pub rules: Vec<Rule>,
}

#[derive(Debug)]
pub struct Subst(pub StringHashMap<Term>);

pub struct Theorem {
    pub stmt: Term,
    pub proof: Ghost<SpecProof>,
}

impl FnName {
    pub fn user(name: &str, arity: usize) -> (res: FnName)
        ensures res@ == SpecFnName::User(name@, arity as int)
    {
        FnName::User(str_to_rc_str(name), arity)
    }

    pub fn eq(&self, other: &Self) -> (res: bool)
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
    // Some utility functions to construct Term
    pub fn var(v: &Var) -> (res: Term)
        ensures res@ == SpecTerm::Var(v@)
    {
        Rc::new(TermX::Var(v.clone()))
    }

    pub fn var_str(v: &str) -> (res: Term)
        ensures res@ == SpecTerm::Var(v@)
    {
        TermX::var(&str_to_rc_str(v))
    }

    pub fn app(name: &FnName, args: Vec<Term>) -> (res: Term)
        ensures res@ == SpecTerm::App(name@, args.deep_view())
    {
        Rc::new(TermX::App(name.clone(), args))
    }

    pub fn app_str(name: &str, args: Vec<Term>) -> (res: Term)
        ensures res@ == SpecTerm::App(SpecFnName::User(name@, args.len() as int), args.deep_view())
    {
        TermX::app(&FnName::user(name, args.len()), args)
    }

    pub fn constant(name: &str) -> (res: Term)
        ensures res@ == SpecTerm::App(SpecFnName::User(name@, 0), seq![])
    {
        let res = TermX::app(&FnName::user(name, 0), vec![]);
        assert(res@->App_1 =~= seq![]);
        res
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
    pub fn eq(&self, other: &Self) -> (res: bool)
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

impl RuleX {
    pub fn new(head: Term, body: Vec<Term>) -> (res: Rule)
        ensures res == (RuleX { head, body })
    {
        Rc::new(RuleX { head, body })
    }
}

impl ProgramX {
    pub fn new(rules: Vec<Rule>) -> (res: Program)
        ensures res.rules == rules
    {
        Rc::new(ProgramX { rules })
    }
}

impl Theorem {
    /// A theorem has the invariant that the ghost proof object is
    /// a valid proof for the statement
    pub open spec fn wf(self, program: SpecProgram) -> bool {
        self@.wf(program)
    }

    /// Build on subproofs via the axiom SpecProof::ApplyRule
    pub fn apply_rule(program: &Program, rule_id: RuleId, subst: &Subst, subproofs: Vec<&Theorem>) -> (res: Option<Theorem>)
        requires
            0 <= rule_id < program.rules.len() &&
            forall |i| 0 <= i < subproofs.len() ==> (#[trigger] subproofs[i]).wf(program@)

        ensures
            res matches Some(thm) ==> thm.wf(program@)
    {
        let rule = &program.rules[rule_id];
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
                rule_id: rule_id as int,
                subst: subst@,
                subproofs: subproofs.deep_view(),
            }),
        })
    }

    /// Check that two terms are equal and apply axiom SpecProof::Refl
    pub fn refl(program: &Program, left: &Term, right: &Term) -> (res: Option<Theorem>)
        ensures
            res matches Some(thm) ==> thm.wf(program@)
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

impl Clone for Theorem {
    fn clone(&self) -> (res: Self)
        ensures self@ == res@
    {
        Theorem {
            stmt: self.stmt.clone(),
            proof: self.proof,
        }
    }
}

impl Subst {
    pub fn new() -> (res: Subst)
        ensures res@.0 =~= Map::<SpecVar, SpecTerm>::empty()
    {
        Subst(StringHashMap::new())
    }

    pub fn get(&self, var: &Var) -> (res: Option<&Term>)
        ensures
            if self@.0.contains_key(var@) {
                res matches Some(term) && term@ == self@.0[var@]
            } else {
                res matches None
            }
    {
        self.0.get(var)
    }

    pub fn insert(&mut self, var: Var, term: Term)
        ensures self@.0 =~= old(self)@.0.insert(var@, term@),
    {
        self.0.insert(rc_str_to_str(&var).to_string(), term);
    }
}

impl Clone for Subst {
    fn clone(&self) -> (res: Self)
        ensures self@.0 == res@.0
    {
        Subst(self.0.clone())
    }
}

}
