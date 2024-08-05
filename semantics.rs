use vstd::prelude::*;

// Operational semantics of Prolog.
// Everything in this file needs to be trusted.
// Reference: https://doi.org/10.1007/978-1-4471-6368-8_8

verus! {

pub type SpecVar = Seq<char>;
pub type SpecFnName = Seq<char>;

#[verifier::ext_equal]
pub enum SpecTerm {
    Var(SpecVar),
    App(SpecFnName, Seq<SpecTerm>),
    BuiltIn(BuiltInName, Seq<SpecTerm>),
}

pub enum BuiltInName {
    Not,
}

pub struct SpecRule {
    pub head: SpecTerm,
    pub body: Seq<SpecTerm>,
}

pub struct SpecProgram {
    pub rules: Seq<SpecRule>,
}

pub struct SpecSubst(pub Map<SpecVar, SpecTerm>);

pub enum SpecTactic {
    Rule(int), // Applying a rule from the program
    BuiltIn(BuiltInName), // Applying a built-in rule
    Rename(SpecSubst), // Rename variables via an injective substitution to variables (SpecSubst::is_var_renaming)
}

pub struct SpecGoal {
    pub subst: SpecSubst,
    pub subgoals: Seq<SpecTerm>,
}

impl SpecSubst {
    pub open spec fn wf(self) -> bool {
        self.dom().is_full()
    }

    /// The identity substitution
    pub open spec fn identity() -> SpecSubst {
        SpecSubst(Map::total(|v| SpecTerm::Var(v)))
    }

    pub open spec fn contains_var(self, v: SpecVar) -> bool {
        self.0.dom().contains(v)
    }

    pub open spec fn get(self, v: SpecVar) -> SpecTerm {
        self.0[v]
    }

    pub open spec fn dom(self) -> Set<SpecVar> {
        self.0.dom()
    }

    pub open spec fn free_vars(self) -> Set<SpecVar> {
        Set::new(|v| exists |u: SpecVar|
            #![trigger self.get(u).free_vars()]
            self.dom().contains(u) && self.get(u).free_vars().contains(v))
    }

    /**
     * Apply `self` to each of the SpecTerms in `other`
     * 
     * self.compose(other) = self . other (e.g. in Haskell)
     */
    pub open spec fn compose(self, other: SpecSubst) -> SpecSubst {
        SpecSubst(other.0.map_values(|t: SpecTerm| t.subst(self)))
    }

    /**
     * Specifies if `self` is a unifier of `t1` and `ť2`
     */
    pub open spec fn is_unifier(self, t1: SpecTerm, t2: SpecTerm) -> bool {
        self.wf() &&
        t1.subst(self) == t2.subst(self)
    }

    /**
     * Specifies the most general unifier of `t1` and `t2`
     */
    pub open spec fn is_mgu(self, t1: SpecTerm, t2: SpecTerm) -> bool {
        self.wf() &&
        self.is_unifier(t1, t2) &&
        forall |other: SpecSubst| other.is_unifier(t1, t2) ==>
            exists |s: SpecSubst| other == s.compose(self)
    }

    /**
     * Injective and only variables in the image
     */
    pub open spec fn is_var_renaming(self) -> bool {
        self.wf() &&
        self.0.is_injective() &&
        forall |v: SpecVar| #[trigger] self.get(v) matches SpecTerm::Var(_)
    }
}

impl SpecTerm {
    /**
     * Get free SpecVariables in a SpecTerm
     * TODO: Using an axiom here due to Verus issue #1222
     */
    pub closed spec fn free_vars(self) -> Set<SpecVar>;
    #[verifier::external_body]
    pub broadcast proof fn axiom_free_vars(self)
        ensures #[trigger] self.free_vars() == match self {
            SpecTerm::Var(v) => Set::new(|u| u == v),
            SpecTerm::App(_, args) | SpecTerm::BuiltIn(_, args) =>
                Set::new(|v| exists |i: int|
                    #![trigger args[i].free_vars()]
                    0 <= i < args.len() && args[i].free_vars().contains(v)),
        }
    {}

    /**
     * SpecSubstitute a SpecTerm
     * TODO: Using an axiom here due to Verus issue #1222
     */
    pub closed spec fn subst(self, subst: SpecSubst) -> SpecTerm;
    #[verifier::external_body]
    pub broadcast proof fn axiom_subst(self, subst: SpecSubst)
        ensures #[trigger] self.subst(subst) == match self {
            SpecTerm::Var(v) => if subst.contains_var(v) { subst.get(v) } else { self },
            SpecTerm::App(f, args) => SpecTerm::App(f, args.map_values(|arg: SpecTerm| arg.subst(subst))),
            SpecTerm::BuiltIn(f, args) => SpecTerm::BuiltIn(f, args.map_values(|arg: SpecTerm| arg.subst(subst))),
        }
    {}
}

impl SpecRule {
    /**
     * Free variables in a rule are the free variables in the head and body
     */
    pub open spec fn free_vars(self) -> Set<SpecVar> {
        self.head.free_vars().union(
            Set::new(|v| exists |i: int|
                #![trigger self.body[i].free_vars()]
                0 <= i < self.body.len() && self.body[i].free_vars().contains(v))
        )
    }
}

impl SpecTactic {
    pub open spec fn wf(self, program: SpecProgram) -> bool {
        match self {
            SpecTactic::Rule(idx) => 0 <= idx < program.rules.len(),
            SpecTactic::BuiltIn(_) => true,
            SpecTactic::Rename(subst) => subst.is_var_renaming(),
        }
    }
}

/**
 * Given a SpecProgram P, we define a reduction on SpecGoal in the following way:
 * 
 *     t1, G ->_P s1[sigma], ..., sn[sigma], G'[sigma]
 * 
 * iff there exists a SpecRule (t2 :- s1, ..., sn) in P such that
 * sigma is the most general unifier of t1 and t2
 * 
 * A goal G is
 * - provable iff G ->^* []
 * - unprovable iff no such reduction exists
 */
impl SpecGoal {
    pub open spec fn wf(self) -> bool {
        self.subst.wf()
    }

    /**
     * A goal is in a final state when there are no subgoals left
     */
    pub open spec fn is_final(self) -> bool {
        self.subgoals.len() == 0
    }

    /**
     * Return a goal with a single subgoal
     */
    pub open spec fn singleton(term: SpecTerm) -> SpecGoal {
        SpecGoal {
            subst: SpecSubst::identity(),
            subgoals: seq![term],
        }
    }

    /**
     * Free variables in the subgoals
     */
    pub open spec fn free_vars(self) -> Set<SpecVar> {
        Set::new(|v| exists |i: int|
            #![trigger self.subgoals[i].free_vars()]
            0 <= i < self.subgoals.len() && self.subgoals[i].free_vars().contains(v))
    }

    pub open spec fn subst(self, subst: SpecSubst) -> SpecGoal {
        SpecGoal {
            subst: subst.compose(self.subst),
            subgoals: self.subgoals.map_values(|t: SpecTerm| t.subst(subst)),
        }
    }

    /**
     * A goal can step by applying to its first subgoal:
     * - A rule from the SpecProgram via SLD resolution, or
     * - A built-in rule, such as negation-as-failure
     */
    pub closed spec fn step(self, program: SpecProgram, tactic: SpecTactic, next: SpecGoal) -> bool;
    #[verifier::external_body]
    pub broadcast proof fn axiom_step(self, program: SpecProgram, tactic: SpecTactic, next: SpecGoal)
        ensures
            #[trigger] self.step(program, tactic, next) == {
                self.wf() &&
                next.wf() &&
                tactic.wf(program) &&
                !self.is_final() && {
                    let subgoal = self.subgoals[0];

                    match tactic {
                        // Applying a rule from the program
                        SpecTactic::Rule(idx) => {
                            let rule = program.rules[idx];

                            // No common variables
                            rule.free_vars().disjoint(self.free_vars()) &&

                            // Exists a mgu
                            exists |unifier: SpecSubst| #![trigger unifier.is_mgu(rule.head, subgoal)] {
                                &&& unifier.is_mgu(rule.head, subgoal)
                                &&& next.subst == unifier.compose(self.subst)
                
                                // Should consume one subgoal and generate |rule.body| many new subgoals
                                &&& next.subgoals.len() == self.subgoals.len() - 1 + rule.body.len()
                                
                                // The unifier should be applied to all of the subgoals
                                &&& (forall |i: int|
                                    0 <= i < next.subgoals.len() ==>
                                    if i < rule.body.len() {
                                        #[trigger] next.subgoals[i] == rule.body[i].subst(unifier)
                                    } else {
                                        next.subgoals[i] == self.subgoals[i - rule.body.len() + 1].subst(unifier)
                                    }
                                )
                            }
                        },

                        // Applying a built-in tactic
                        SpecTactic::BuiltIn(name) => match name {
                            // \+term holds when there is no solution for term
                            BuiltInName::Not =>
                                subgoal matches SpecTerm::BuiltIn(BuiltInName::Not, args) && args.len() == 1 && {
                                    SpecGoal::singleton(args[0]).has_no_solution(program)
                                }
                        }

                        // Apply a renaming substitution to each subgoal and the substitution
                        SpecTactic::Rename(subst) => next == self.subst(subst)
                    }
                }
            }
    {}

    pub open spec fn has_no_solution(self, program: SpecProgram) -> bool {
        forall |trace: Seq<SpecTactic>, final_subst: SpecSubst| !self.has_solution(program, trace, final_subst)
    }

    /**
     * A goal has a solution when there is a finite trace reaching a success state
     */
    pub open spec fn has_solution(self, program: SpecProgram, trace: Seq<SpecTactic>, final_subst: SpecSubst) -> bool
        decreases trace.len()
    {
        // if self.is_final() {
        //     trace.len() == 0 && final_subst == self.subst
        // } else {
        //     trace.len() != 0 &&
        //     (exists |next: SpecGoal|
        //         #[trigger] self.step(program, trace[0], next) &&
        //         next.has_solution(program, trace.drop_first(), final_subst))
        // }

        if trace.len() == 0 {
            self.subst == final_subst && self.is_final()
        } else {
            exists |next: SpecGoal|
                #[trigger] self.step(program, trace[0], next) &&
                next.has_solution(program, trace.drop_first(), final_subst)
        }
    }

    /**
     * Applying multiple steps
     */
    pub open spec fn reach(self, program: SpecProgram, trace: Seq<SpecTactic>, reachable: SpecGoal) -> bool
        decreases trace.len()
    {
        if trace.len() == 0 {
            self == reachable
        } else {
            exists |next: SpecGoal|
                #[trigger] self.step(program, trace[0], next) &&
                next.reach(program, trace.drop_first(), reachable)
        }
    }
}

}

verus! {

proof fn test() {
    broadcast use SpecTerm::axiom_subst;
    broadcast use SpecTerm::axiom_free_vars;
    
    let c1 = SpecTerm::App("c1".view(), seq![]);
    let c2 = SpecTerm::App("c2".view(), seq![]);
    let v1 = SpecTerm::Var("v1".view());
    let v2 = SpecTerm::Var("v2".view());

    let t1 = SpecTerm::App("f".view(), seq![c1, v1]);
    let t2 = SpecTerm::App("f".view(), seq![c1, c2]);
    let t3 = SpecTerm::App("f".view(), seq![c1, v1]);

    let subst = SpecSubst(Map::empty().insert("v1".view(), c2));

    assert(c1.subst(subst)->App_0 == c1->App_0);
    assert(c1.subst(subst)->App_1 == c1->App_1);
    assert(c1.subst(subst) == c1);
    assert(v1.subst(subst) == c2);

    assert(t1.subst(subst)->App_0 == t2->App_0);
    assert(t1.subst(subst)->App_1 == t2->App_1);
    assert(t1.subst(subst) == t2);
    // Why does this not work?
    // assert(t1.subst(subst) =~~= t2);

    // TODO: need to use this trigger
    let _ = t1->App_1[1].free_vars();
    assert(t1.free_vars() == Set::empty().insert("v1".view()));

    let program = SpecProgram {
        rules: seq![
            SpecRule {
                head: SpecTerm::App("edge".view(), seq![
                    SpecTerm::App("n1".view(), seq![]),
                    SpecTerm::App("n2".view(), seq![]),
                ]),
                body: seq![],
            },
            SpecRule {
                head: SpecTerm::App("edge".view(), seq![
                    SpecTerm::App("n2".view(), seq![]),
                    SpecTerm::App("n3".view(), seq![]),
                ]),
                body: seq![],
            },
        ],
    };
}

}
