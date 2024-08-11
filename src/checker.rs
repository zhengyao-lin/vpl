use vstd::prelude::*;
use std::rc::Rc;

use urlencoding;

use crate::containers::StringHashMap;
use crate::proof::*;
use crate::polyfill::*;
use crate::matching::*;

// A dynamic builder of proofs with verified checks

verus! {

broadcast use TermX::axiom_view, SpecTerm::axiom_subst, SpecTerm::axiom_matches;

pub type Var = Rc<str>;
pub type UserFnName = Rc<str>;
pub type RuleId = usize;
pub type Arity = usize;

/// TODO: right now we limit integers to 64-bit
/// but Prolog actually supports arbitrary precision integers
pub type LiteralInt = i64;
pub type LiteralString = Rc<str>;

#[derive(Debug)]
pub enum FnName {
    // User-defined symbol: (name, arity)
    User(UserFnName, Arity),
    Nil,
    Cons,
    Directive,
}

#[derive(Debug)]
pub enum Literal {
    Int(LiteralInt),
    String(LiteralString),
}

pub type Term = Rc<TermX>;
#[derive(Debug)]
pub enum TermX {
    Var(Var),
    Literal(Literal),
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
            (FnName::Nil, FnName::Nil) => true,
            (FnName::Cons, FnName::Cons) => true,
            (FnName::Directive, FnName::Directive) => true,
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
            FnName::Nil => FnName::Nil,
            FnName::Cons => FnName::Cons,
            FnName::Directive => FnName::Directive,
        }
    }
}

impl Literal {
    pub fn eq(&self, other: &Self) -> (res: bool)
        ensures res == (self@ == other@)
    {
        match (self, other) {
            (Literal::Int(i1), Literal::Int(i2)) => i1 == i2,
            (Literal::String(s1), Literal::String(s2)) => rc_str_eq(s1, s2),
            _ => false,
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

            TermX::Literal(..) => term.clone(),

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
    
    pub fn eq(&self, other: &Self) -> (res: bool)
        ensures res == (self@ == other@)
    {
        match (self, other) {
            (TermX::Var(v1), TermX::Var(v2)) => rc_str_eq(v1, v2),
            (TermX::Literal(l1), TermX::Literal(l2)) => l1.eq(l2),
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
                        args1.len() == args2.len(),
                        args1.deep_view() =~= self@->App_1,
                        args2.deep_view() =~= other@->App_1,
                        forall |j: int| 0 <= j < i ==> (#[trigger] args1[j as int])@ == args2[j as int]@,
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

    /// Corresponds to SpecTerm::as_list
    pub fn as_list(&self) -> (res: Option<Vec<&Term>>)
        ensures res matches Some(list) ==> self@.as_list() =~= Some(list.deep_view())
    {
        match self {
            TermX::App(FnName::Nil, args) =>
                if args.len() == 0 {
                    Some(vec![])
                } else {
                    None
                },

            TermX::App(FnName::Cons, args) =>
                if args.len() == 2 {
                    match (&args[1]).as_list() {
                        Some(mut tail) => {
                            // TODO: innefficient
                            tail.insert(0, &args[0]);
                            Some(tail)
                        }
                        None => None,
                    }
                } else {
                    None
                },

            _ => None,
        }
    }

    /// Check if `self` occurs in the list of terms
    pub fn is_member(&self, list: &Vec<&Term>) -> (res: bool)
        ensures res == list.deep_view().contains(self@)
    {
        for i in 0..list.len()
            invariant forall |j| 0 <= j < i ==> self@ != #[trigger] list.deep_view()[j]
        {
            if self.eq(list[i]) {
                assert(list.deep_view()[i as int] == self@);
                return true;
            }
        }
        return false;
    }

    /// Corresponds to SpecTerm::not_unifiable
    pub fn not_unifiable(&self, other: &Term) -> (res: bool)
        ensures res == self@.not_unifiable(other@)
    {
        match (self, rc_as_ref(other)) {
            (TermX::Literal(l1), TermX::Literal(l2)) => !l1.eq(l2),

            // Distinct head symbol, or non-unifiable subterms
            (TermX::App(f1, args1), TermX::App(f2, args2)) => {
                if !f1.eq(f2) || args1.len() != args2.len() {
                    return true;
                }

                // Check if any subterms are not unifiable
                for i in 0..args1.len()
                    invariant
                        args1.len() == args2.len(),
                        self@ =~= SpecTerm::App(f1@, args1.deep_view()),
                        other@ =~= SpecTerm::App(f2@, args2.deep_view()),
                        forall |j| 0 <= j < i ==> !(#[trigger] args1[j])@.not_unifiable(args2[j]@),
                {
                    if (&args1[i]).not_unifiable(&args2[i]) {
                        assert(self@->App_1[i as int].not_unifiable(other@->App_1[i as int]));
                        return true;
                    }
                }

                false
            }

            (TermX::Literal(..), TermX::App(..)) => true,
            (TermX::App(..), TermX::Literal(..)) => true,

            _ => false,
        }
    }

    /// A helper function to check the arity and name
    /// of the head symbol of the term; and returns the arguments
    /// Corresponds to SpecTerm::headed_by
    pub fn headed_by<'a, 'b>(&'a self, expected_name: &'b str, expected_arity: usize) -> (res: Option<&'a Vec<Term>>)
        ensures match res {
            Some(res) => Some(res.deep_view()) == self@.headed_by(expected_name, expected_arity as int),
            None => self@.headed_by(expected_name, expected_arity as int).is_none(),
        }
    {
        match self {
            TermX::App(FnName::User(name, arity), args) =>
                if *arity == args.len() &&
                    rc_str_eq_str(name, expected_name) &&
                    *arity == expected_arity {
                    Some(args)
                } else {
                    None
                },
            _ => None,
        }
    }

    /// Corresponds to SpecTerm::eval_arith
    /// In addition, this function needs to check for overflow
    pub fn eval_arith(&self) -> (res: Option<i64>)
        // NOTE: Since i64 may overflow, if we get res == None
        // we can't deduce that the spec should also be None
        ensures res matches Some(i) ==> self@.eval_arith() == Some(i as int)
    {
        if let TermX::Literal(Literal::Int(i)) = self {
            Some(*i)
        } else if let Some(args) = self.headed_by(FN_NAME_ADD, 2) {
            if let (Some(lhs), Some(rhs)) = ((&args[0]).eval_arith(), (&args[1]).eval_arith()) {
                lhs.checked_add(rhs)
            } else {
                None
            }
        } else if let Some(args) = self.headed_by(FN_NAME_SUB, 2) {
            if let (Some(lhs), Some(rhs)) = ((&args[0]).eval_arith(), (&args[1]).eval_arith()) {
                lhs.checked_sub(rhs)
            } else {
                None
            }
        } else if let Some(args) = self.headed_by(FN_NAME_MUL, 2) {
            if let (Some(lhs), Some(rhs)) = ((&args[0]).eval_arith(), (&args[1]).eval_arith()) {
                lhs.checked_mul(rhs)
            } else {
                None
            }
        } else {
            None
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
            0 <= rule_id < program.rules.len(),
            forall |i| 0 <= i < subproofs.len() ==> (#[trigger] subproofs[i]).wf(program@),

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
                rule.body.len() == subproofs.len(),
                forall |j| 0 <= j < i ==> (#[trigger] rule.body[j])@.subst(subst@) == subproofs[j].stmt@,
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

    pub fn true_intro(program: &Program) -> (res: Theorem)
        ensures res.wf(program@)
    {
        Theorem {
            stmt: TermX::app(&FnName::user(FN_NAME_TRUE, 0), vec![]),
            proof: Ghost(SpecProof::TrueIntro),
        }
    }

    /// Introduce (a, b) given proofs of both a and b
    pub fn and_intro(program: &Program, left: &Theorem, right: &Theorem) -> (res: Theorem)
        requires left.wf(program@) && right.wf(program@)
        ensures res.wf(program@)
    {
        Theorem {
            stmt: TermX::app(&FnName::user(FN_NAME_AND, 2), vec![left.stmt.clone(), right.stmt.clone()]),
            proof: Ghost(SpecProof::AndIntro(Box::new(left@), Box::new(right@))),
        }
    }

    /// Introduce (a; b) given a proof a
    pub fn or_intro_left(program: &Program, subproof: &Theorem, right: &Term) -> (res: Theorem)
        requires subproof.wf(program@)
        ensures res.wf(program@)
    {
        Theorem {
            stmt: TermX::app(&FnName::user(FN_NAME_OR, 2), vec![subproof.stmt.clone(), right.clone()]),
            proof: Ghost(SpecProof::OrIntroLeft(Box::new(subproof@))),
        }
    }

    /// Introduce (a; b) given a proof b
    pub fn or_intro_right(program: &Program, left: &Term, subproof: &Theorem) -> (res: Theorem)
        requires subproof.wf(program@)
        ensures res.wf(program@)
    {
        Theorem {
            stmt: TermX::app(&FnName::user(FN_NAME_OR, 2), vec![left.clone(), subproof.stmt.clone()]),
            proof: Ghost(SpecProof::OrIntroRight(Box::new(subproof@))),
        }
    }

    /// Construct a proof for forall(member(loop_var, list_term), goal), see SpecProof::ForallMember for more detail
    pub fn forall_member(program: &Program, outer_goal: &Term, subproofs: Vec<&Theorem>) -> (res: Option<Theorem>)
        ensures
            res matches Some(thm) ==> thm.stmt@ == outer_goal@ && thm.wf(program@)
    {
        // Check that outer_goal is of the form forall(member(loop_var, list_term), goal)
        let (loop_var, list_term, goal) =
            if let Some(forall_args) = outer_goal.headed_by(FN_NAME_FORALL, 2) {
                if let Some(member_args) = (&forall_args[0]).headed_by(FN_NAME_MEMBER, 2) {
                    if let TermX::Var(loop_var) = rc_as_ref(&member_args[0]) {
                        (loop_var, &member_args[1], &forall_args[1])
                    } else {
                        return None;
                    }
                } else {
                    return None;
                }
            } else {
                return None;
            };

        match list_term.as_list() {
            None => None,
            Some(list) => {
                if list.len() != subproofs.len() {
                    return None;
                }

                // For each subproof, check that the statement is exactly
                // Goal[loop_var |-> list[i]]
                for i in 0..list.len()
                    invariant
                        list.len() == subproofs.len(),

                        forall |j| 0 <= j < i ==> {
                            let subst = SpecSubst(map!{ loop_var@ => list[j]@ });
                            let subst_goal = goal@.subst(subst);
                            (#[trigger] subproofs[j]).stmt@ == subst_goal
                        },
                {
                    let mut subst = Subst::new();
                    subst.insert(loop_var.clone(), list[i].clone());
                    let subst_goal = TermX::subst(goal, &subst);

                    if !(&subproofs[i].stmt).eq(&subst_goal) {
                        return None;
                    }
                }

                Some(Theorem {
                    stmt: outer_goal.clone(),
                    proof: Ghost(SpecProof::ForallMember(subproofs.deep_view())),
                })
            }
        }
    }

    /// Match pattern against every head of a rule
    /// and check the assumption that each rule head (program.only_unifiable_with_base)
    /// - Either is matched by pattern and is a fact
    /// - Or is not unifiable with pattern
    /// 
    /// Essentially this exhausts all possible solutions to pattern
    /// and substitute that solution into template,
    /// assuming that the pattern is headed by a "base" predicate symbol
    fn match_subst_base_predicates(program: &Program, pattern: &Term, template: &Term) -> (res: Option<Vec<Term>>)
        ensures
            res matches Some(insts) ==> {
                &&& program@.only_unifiable_with_base(pattern@)
                &&& filter_map(program@.rules, |rule: SpecRule| {
                    if let Some(subst) = pattern@.matches(rule.head) {
                        Some(template@.subst(subst))
                    } else {
                        None
                    }
                }) =~= insts.deep_view()
            }
    {
        let ghost filter = |rule: SpecRule| {
            if let Some(subst) = pattern@.matches(rule.head) {
                Some(template@.subst(subst))
            } else {
                None
            }
        };

        let mut insts = vec![];

        for i in 0..program.rules.len()
            invariant
                // filter stays unchanged
                filter == |rule: SpecRule| {
                    if let Some(subst) = pattern@.matches(rule.head) {
                        Some(template@.subst(subst))
                    } else {
                        None
                    }
                },

                // A prefix version of program.only_unifiable_with_base
                forall |j: int| 0 <= j < i ==>
                    (#[trigger] program@.rules[j]).matching_or_not_unifiable(pattern@),

                // The first i rules are corrected processed
                filter_map(program@.rules.take(i as int), filter) =~= insts.deep_view(),
        {
            let rule = &program.rules[i];
            if rule.body.len() != 0 {
                // Non-fact rules should not unify with the pattern
                if !pattern.not_unifiable(&rule.head) {
                    return None;
                }

                proof {
                    pattern@.lemma_non_unifiable_to_non_matching(rule@.head);
                    lemma_filter_map_skip(program@.rules, filter, i as int);
                }
            } else {
                // Any fact should either be matched by pattern
                // or not unifiable (i.e. nothing in between)
                let mut subst = Subst::new();
                let ghost old_subst = subst@;
                if let Ok(..) = TermX::match_terms(&mut subst, &pattern, &rule.head) {
                    insts.push(TermX::subst(template, &subst));

                    proof {
                        // Append the mapped element to the filtered list
                        lemma_filter_map_no_skip(program@.rules, filter, i as int);
                        let matches_subst = pattern@.matches(rule@.head).unwrap();
                        old_subst.lemma_merge_empty_left(matches_subst);
                    }
                } else if !pattern.not_unifiable(&rule.head) {
                    return None;
                } else {
                    proof {
                        // No change to the filtered list
                        lemma_filter_map_skip(program@.rules, filter, i as int);
                    }
                }
            }
        }

        assert(program@.rules.take(program.rules.len() as int) == program@.rules);

        Some(insts)
    }

    /// Proof-check base case of findall
    pub fn findall_base(program: &Program, goal: &Term) -> (res: Option<Theorem>)
        ensures
            res matches Some(thm) ==> thm.stmt@ == goal@ && thm.wf(program@)
    {
        if let Some(args) = goal.headed_by(FN_NAME_FINDALL, 3) {
            let template = &args[0];
            let pattern = &args[1];

            if let Some(list) = (&args[2]).as_list() {
                if let Some(insts) = Self::match_subst_base_predicates(program, pattern, template) {
                    // Check that the instances coincides with the list
                    if insts.len() != list.len() {
                        return None;
                    }

                    for i in 0..insts.len()
                        invariant
                            insts.len() == list.len(),
                            forall |j| #![auto] 0 <= j < i ==> insts[j]@ == list[j]@
                    {
                        if !(&insts[i]).eq(list[i]) {
                            return None;
                        }
                    }

                    return Some(Theorem {
                        stmt: goal.clone(),
                        proof: Ghost(SpecProof::BuiltIn),
                    });
                }
            }
        }

        None
    }

    /// Apply and proof-check SpecProof::ForallBase
    pub fn forall_base(program: &Program, goal: &Term, subproofs: Vec<&Theorem>) -> (res: Option<Theorem>)
        ensures
            res matches Some(thm) ==> thm.stmt@ == goal@ && thm.wf(program@)
    {
        if let Some(args) = goal.headed_by(FN_NAME_FORALL, 2) {
            let pattern = &args[0];
            let template = &args[1];

            if let Some(insts) = Self::match_subst_base_predicates(program, pattern, template) {
                if insts.len() != subproofs.len() {
                    return None;
                }

                // Check that the instances match the statements of the subproofs
                for i in 0..insts.len()
                    invariant
                        insts.len() == subproofs.len(),
                        forall |j| #![auto] 0 <= j < i ==> insts[j]@ == subproofs[j].stmt@,
                {
                    if !(&insts[i]).eq(&subproofs[i].stmt) {
                        return None;
                    }
                }

                return Some(Theorem {
                    stmt: goal.clone(),
                    proof: Ghost(SpecProof::ForallBase(subproofs.deep_view())),
                });
            }
        }

        None
    }

    /// Try applying the axiom of a domain function for ints, strings, or lists
    pub fn try_built_in(program: &Program, goal: &Term) -> (res: Option<Theorem>)
        ensures
            res matches Some(thm) ==> thm.stmt@ == goal@ && thm.wf(program@)
    {
        if let Some(args) = goal.headed_by(FN_NAME_EQ, 2) {
            if (&args[0]).eq(&args[1]) {
                return Some(Theorem { stmt: goal.clone(), proof: Ghost(SpecProof::BuiltIn) });
            }
        } else if let Some(args) = goal.headed_by(FN_NAME_EQUIV, 2) {
            if (&args[0]).eq(&args[1]) {
                return Some(Theorem { stmt: goal.clone(), proof: Ghost(SpecProof::BuiltIn) });
            }
        } else if let Some(args) = goal.headed_by(FN_NAME_NOT_EQ, 2) {
            if (&args[0]).not_unifiable(&args[1]) {
                return Some(Theorem { stmt: goal.clone(), proof: Ghost(SpecProof::BuiltIn) });
            }
        } else if let Some(args) = goal.headed_by(FN_NAME_NOT_EQUIV, 2) {
            if !(&args[0]).eq(&args[1]) {
                return Some(Theorem { stmt: goal.clone(), proof: Ghost(SpecProof::BuiltIn) });
            }
        } else if let Some(args) = goal.headed_by(FN_NAME_LENGTH, 2) {
            // length(L, N) iff length of L is N
            if let (Some(list), TermX::Literal(Literal::Int(i))) = ((&args[0]).as_list(), rc_as_ref(&args[1])) {
                // TODO: better way to check overflow
                if *i >= 0 && *i <= u32::MAX as i64 && list.len() == *i as usize {
                    return Some(Theorem { stmt: goal.clone(), proof: Ghost(SpecProof::BuiltIn) });
                }
            }
        } else if let Some(args) = goal.headed_by(FN_NAME_MEMBER, 2) {
            // member(X, L) iff X is in L
            if let Some(list) = (&args[1]).as_list() {
                if (&args[0]).is_member(&list) {
                    return Some(Theorem { stmt: goal.clone(), proof: Ghost(SpecProof::BuiltIn) });
                }
            }
        } else if let Some(args) = goal.headed_by(FN_NAME_NOT, 1) {
            // \+P holds if P is not unifiable with head of any rule
            for i in 0..program.rules.len()
                invariant
                    args.len() == 1,
                    forall |j| 0 <= j < i ==> (#[trigger] program.rules[j]).head@.not_unifiable(args[0]@)
            {
                if !(&program.rules[i].head).not_unifiable(&args[0]) {
                    return None;
                }
            }

            return Some(Theorem { stmt: goal.clone(), proof: Ghost(SpecProof::BuiltIn) });
        } else if let Some(_) = goal.headed_by(FN_NAME_FINDALL, 3) {
            return Self::findall_base(program, goal);
        } else if let Some(args) = goal.headed_by(FN_NAME_GT, 2) {
            if let (Some(lhs), Some(rhs)) = ((&args[0]).eval_arith(), (&args[1]).eval_arith()) {
                if lhs > rhs {
                    return Some(Theorem { stmt: goal.clone(), proof: Ghost(SpecProof::BuiltIn) });
                }
            }
        } else if let Some(args) = goal.headed_by(FN_NAME_GE, 2) {
            if let (Some(lhs), Some(rhs)) = ((&args[0]).eval_arith(), (&args[1]).eval_arith()) {
                if lhs >= rhs {
                    return Some(Theorem { stmt: goal.clone(), proof: Ghost(SpecProof::BuiltIn) });
                }
            }
        } else if let Some(args) = goal.headed_by(FN_NAME_LT, 2) {
            if let (Some(lhs), Some(rhs)) = ((&args[0]).eval_arith(), (&args[1]).eval_arith()) {
                if lhs < rhs {
                    return Some(Theorem { stmt: goal.clone(), proof: Ghost(SpecProof::BuiltIn) });
                }
            }
        } else if let Some(args) = goal.headed_by(FN_NAME_LE, 2) {
            if let (Some(lhs), Some(rhs)) = ((&args[0]).eval_arith(), (&args[1]).eval_arith()) {
                if lhs <= rhs {
                    return Some(Theorem { stmt: goal.clone(), proof: Ghost(SpecProof::BuiltIn) });
                }
            }
        } else if let Some(args) = goal.headed_by(FN_NAME_IS, 2) {
            if let Some(rhs) = (&args[1]).eval_arith() {
                if (&args[0]).eq(&Rc::new(TermX::Literal(Literal::Int(rhs)))) {
                    return Some(Theorem { stmt: goal.clone(), proof: Ghost(SpecProof::BuiltIn) });
                }
            }
        } else if let Some(args) = goal.headed_by(FN_NAME_EVAL_EQ, 2) {
            if let (Some(lhs), Some(rhs)) = ((&args[0]).eval_arith(), (&args[1]).eval_arith()) {
                if lhs == rhs {
                    return Some(Theorem { stmt: goal.clone(), proof: Ghost(SpecProof::BuiltIn) });
                }
            }
        } else if let Some(args) = goal.headed_by(FN_NAME_EVAL_NOT_EQ, 2) {
            if let (Some(lhs), Some(rhs)) = ((&args[0]).eval_arith(), (&args[1]).eval_arith()) {
                if lhs != rhs {
                    return Some(Theorem { stmt: goal.clone(), proof: Ghost(SpecProof::BuiltIn) });
                }
            }
        } else if let Some(args) = goal.headed_by(FN_NAME_NONVAR, 1) {
            match rc_as_ref(&args[0]) {
                TermX::Var(..) => return None,
                _ => return Some(Theorem { stmt: goal.clone(), proof: Ghost(SpecProof::BuiltIn) }),
            }
        } else if let Some(args) = goal.headed_by(FN_NAME_VAR, 1) {
            match rc_as_ref(&args[0]) {
                TermX::Var(..) => return Some(Theorem { stmt: goal.clone(), proof: Ghost(SpecProof::BuiltIn) }),
                _ => return None,
            }
        } else if let Some(args) = goal.headed_by(FN_NAME_ATOM_STRING, 2) {
            match rc_as_ref(&args[1]) {
                (TermX::Literal(Literal::String(string))) => {
                    if (&args[0]).headed_by(rc_str_to_str(string), 0).is_some() {
                        return Some(Theorem { stmt: goal.clone(), proof: Ghost(SpecProof::BuiltIn) });
                    } else {
                        return None;
                    }
                }
                _ => return None,
            }
        } else if let Some(args) = goal.headed_by(FN_NAME_STRING_CHARS, 2) {
            match rc_as_ref(&args[0]) {
                (TermX::Literal(Literal::String(string))) => {
                    if let Some(chars) = (&args[1]).as_list() {
                        if chars.len() != string.unicode_len() {
                            return None;
                        }

                        // Compare each char
                        // TODO: get_char and unicode_len are O(n)
                        // Verus doesn't support iterator string.chars() yet
                        for i in 0..chars.len()
                            invariant
                                chars.len() == string@.len(),
                                forall |j| 0 <= j < i ==>
                                    (#[trigger] chars[j])@ =~= SpecTerm::App(SpecFnName::User(seq![string@[j as int]], 0), seq![]),
                        {
                            match rc_as_ref(&chars[i]) {
                                TermX::App(FnName::User(s, arity), args) => {
                                    if *arity == 0 && args.len() == 0 &&
                                        s.unicode_len() == 1 && s.get_char(0) == string.get_char(i) {
                                        assert(s@ =~= seq![string@[i as int]]);
                                        assert(args.deep_view() =~= seq![]);
                                    } else {
                                        return None;
                                    }
                                }
                                _ => return None,
                            }
                        }

                        return Some(Theorem { stmt: goal.clone(), proof: Ghost(SpecProof::BuiltIn) });
                    } else {
                        return None;
                    }
                }
                _ => return None,
            }
        } else if let Some(args) = goal.headed_by(FN_NAME_SUB_STRING, 5) {
            match (
                rc_as_ref(&args[0]),
                rc_as_ref(&args[1]),
                rc_as_ref(&args[2]),
                rc_as_ref(&args[3]),
                rc_as_ref(&args[4]),
            ) {
                (
                    TermX::Literal(Literal::String(string)),
                    TermX::Literal(Literal::Int(before)),
                    TermX::Literal(Literal::Int(len)),
                    TermX::Literal(Literal::Int(after)),
                    TermX::Literal(Literal::String(substring)),
                ) => {
                    if *before < 0 || *len < 0 || *after < 0 {
                        return None;
                    }

                    // TODO: these overflow checks are not precise
                    if *before > u32::MAX as i64 || *len > u32::MAX as i64 || *after > u32::MAX as i64 {
                        return None;
                    }

                    if let Some(end) = (*before).checked_add(*len) {
                        if let Some(sum) = end.checked_add(*after) {
                            if sum > u32::MAX as i64 {
                                return None;
                            }

                            if string.unicode_len() != sum as usize {
                                return None;
                            }

                            if substring.unicode_len() != *len as usize {
                                return None;
                            }
        
                            if *len != 0 {
                                if !rc_str_eq_str(substring, string.substring_char(*before as usize, end as usize)) {
                                    return None;
                                }
                            }
            
                            return Some(Theorem { stmt: goal.clone(), proof: Ghost(SpecProof::BuiltIn) });
                        }
                    } else {
                        return None;
                    }
                }
                _ => return None,
            }
        } else if let Some(args) = goal.headed_by(FN_NAME_REVERSE, 2) {
            match ((&args[0]).as_list(), (&args[1]).as_list()) {
                (Some(mut list), Some(reversed)) => {
                    let ghost old_list = list.deep_view();
                    vec_reverse(&mut list);

                    assert(old_list.reverse() == list.deep_view());

                    // Check that list == reversed
                    if list.len() != reversed.len() {
                        return None;
                    }

                    for i in 0..list.len()
                        invariant
                            list.len() == reversed.len(),
                            forall |j| 0 <= j < i ==> #[trigger] list[j]@ == reversed[j]@,
                    {
                        if !list[i].eq(reversed[i]) {
                            return None;
                        }
                    }

                    return Some(Theorem { stmt: goal.clone(), proof: Ghost(SpecProof::BuiltIn) });
                }
                _ => return None,
            }
        }

        Self::unverified_builtins(program, goal)
    }

    /// Some unverified built-in functions due to lack of specs
    /// TODO: move this to the verified check
    #[verifier::external_body]
    fn unverified_builtins(program: &Program, goal: &Term) -> (res: Option<Theorem>)
        ensures
            res matches Some(thm) ==> thm.stmt@ == goal@ && thm.wf(program@)
    {
        if let Some(args) = goal.headed_by("string_lower", 2) {
            if let (
                TermX::Literal(Literal::String(s1)),
                TermX::Literal(Literal::String(s2)),
            ) = (rc_as_ref(&args[0]), rc_as_ref(&args[1])) {
                if s1.to_lowercase() == s2.as_ref() {
                    return Some(Theorem { stmt: goal.clone(), proof: Ghost(SpecProof::BuiltIn) });
                }
            }
        } else if let Some(args) = goal.headed_by("uri_encoded", 3) {
            if let (
                TermX::App(FnName::User(s1, 0), ..),
                TermX::Literal(Literal::String(s2)),
            ) = (rc_as_ref(&args[1]), rc_as_ref(&args[2])) {
                // TODO: fix this
                if urlencoding::encode(s1) == s2.as_ref() {
                    return Some(Theorem { stmt: goal.clone(), proof: Ghost(SpecProof::BuiltIn) });
                }
            }
        }

        // print("unsupported built-in: "); println(goal);
        // return Some(Theorem { stmt: goal.clone(), proof: Ghost(SpecProof::BuiltIn) });
        None
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
        ensures res@.0 =~= Map::<SpecVar, SpecTerm>::empty() && res@.is_empty()
    {
        Subst(StringHashMap::new())
    }

    pub fn get(&self, var: &Var) -> (res: Option<&Term>)
        ensures
            self@.contains_var(var@) == res.is_some() &&
            (if self@.contains_var(var@) {
                res matches Some(term) && term@ == self@.get(var@)
            } else {
                res matches None
            })
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
