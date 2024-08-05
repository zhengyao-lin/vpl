use vstd::prelude::*;

use crate::semantics::*;

// A simple Prolog solevr (which still lives in spec mode)

verus! {

impl SpecGoal {
    /**
     * Reaching a final goal implies having a solution
     */
    pub proof fn lemma_reach_final_solution(self, program: SpecProgram, trace: Seq<SpecTactic>, reachable: SpecGoal)
        requires self.reach(program, trace, reachable) && reachable.is_final()
        ensures self.has_solution(program, trace, reachable.subst)
        decreases trace.len()
    {
        if trace.len() > 0 {
            let next = choose |next: SpecGoal|
                #[trigger] self.step(program, trace[0], next) &&
                next.reach(program, trace.drop_first(), reachable);
                
            next.lemma_reach_final_solution(program, trace.drop_first(), reachable);
        }
    }

    /**
     * Apply one more tactic at the end of a trace
     */
    pub proof fn lemma_reach_append_next(
        self,
        program: SpecProgram,
        trace: Seq<SpecTactic>,
        reachable1: SpecGoal,
        next_tactic: SpecTactic,
        reachable2: SpecGoal,
    )
        requires
            self.reach(program, trace, reachable1) &&
            reachable1.step(program, next_tactic, reachable2)
        
        ensures
            self.reach(program, trace + seq![next_tactic], reachable2)
    {
        assume(false);
    }
}

pub struct SpecSolver {
    pub program: SpecProgram,
    pub goal_stack: Seq<SpecGoal>,
    pub num_sols: int,

    pub goal_traces: Seq<Seq<SpecTactic>>,
    pub init_goal: SpecGoal,
}

impl SpecSolver {
    pub open spec fn inv(self) -> bool {
        &&& self.num_sols >= 0

        // Each goal is well-formed
        &&& self.init_goal.wf()
        &&& forall |i: int| 0 <= i < self.goal_stack.len() ==> (#[trigger] self.goal_stack[i]).wf()
    
        // Every intermediate goal in the stack is reachable from the initial goal using
        // the corresponding trace
        &&& self.goal_traces.len() == self.goal_stack.len()
        &&& forall |i: int| 0 <= i < self.goal_stack.len() ==>
            self.init_goal.reach(self.program, #[trigger] self.goal_traces[i], #[trigger] self.goal_stack[i])
    }

    pub open spec fn new(program: SpecProgram, init_goal: SpecGoal) -> SpecSolver {
        SpecSolver {
            program,
            goal_stack: seq![init_goal],
            num_sols: 0,
            goal_traces: seq![seq![]],
            init_goal,
        }
    }

    pub proof fn spec_new(program: SpecProgram, init_goal: SpecGoal)
        requires init_goal.wf()
        ensures SpecSolver::new(program, init_goal).inv()
    {}

    /**
     * In each iteration, pop a goal from the stack,
     * iterate through the rules, try to apply them, and push the result to the stack.
     */
    pub closed spec fn iter(self) -> (SpecSolver, Option<(SpecGoal, Seq<SpecTactic>)>) {
        if self.goal_stack.len() == 0 {
            (self, None)
        } else {
            let goal = self.goal_stack.last();
            let trace = self.goal_traces.last();

            if goal.is_final() {
                (SpecSolver {
                    goal_stack: self.goal_stack.drop_last(),
                    goal_traces: self.goal_traces.drop_last(),
                    ..self
                }, Some((goal, trace)))
            } else {
                // For each rule in the reverse order:
                // - Rename the variables in the goal
                // - Unify against and apply the rule
                // - Push the result to the stack
                (self.apply_all_rules(goal, trace, self.program.rules.len() - 1), None)
            }
        }
    }

    pub proof fn spec_iter(self)
        requires self.inv()
        ensures ({
            let (next, sol_opt) = self.iter();
            
            &&& next.inv()
            &&& sol_opt matches Some((sol, trace)) ==> self.init_goal.has_solution(self.program, trace, sol.subst)
        })
    {
        let (next, sol_opt) = self.iter();

        match sol_opt {
            Some((sol, trace)) => {
                self.init_goal.lemma_reach_final_solution(self.program, trace, sol);
            }
            None => {
                if self.goal_stack.len() != 0 {
                    let goal = self.goal_stack.last();
                    let trace = self.goal_traces.last();
                    self.spec_apply_all_rules(goal, trace, self.program.rules.len() - 1);
                }
            }
        }
    }

    /**
     * Generate a renaming substitution for the `goal_vars` such that
     * after substituted, the variables in the goal are disjoint from `rule_vars`
     * 
     * TODO: implement this
     */
    spec fn gen_fresh_vars(rule_vars: Set<SpecVar>, goal_vars: Set<SpecVar>) -> SpecSubst;

    #[verifier::external_body]
    proof fn spec_gen_fresh_vars(rule_vars: Set<SpecVar>, goal_vars: Set<SpecVar>)
        ensures ({
            let subst = Self::gen_fresh_vars(rule_vars, goal_vars);
            subst.is_var_renaming() &&
            forall |v: SpecVar| #[trigger] goal_vars.contains(v) ==> !rule_vars.contains(subst.get(v)->Var_0)
        })
    {}

    spec fn apply_all_rules(self, goal: SpecGoal, trace: Seq<SpecTactic>, idx: int) -> SpecSolver
        decreases idx + 1
    {
        if idx < 0 {
            self
        } else {
            let rule = self.program.rules[idx];
            let rule_vars = rule.free_vars();

            let first_subgoal = goal.subgoals[0];
            let goal_vars = goal.free_vars();

            // Rename overlapping variables in the goal
            let renaming = Self::gen_fresh_vars(rule_vars, goal_vars);
            let renamed_goal = goal.subst(renaming);

            // Unify against the rule
            let next_state = match Self::apply_rule(self.program, renamed_goal, idx) {
                None => self, // move on to the next rule
                Some(new_goal) => {
                    let new_trace = trace + seq![SpecTactic::Rename(renaming), SpecTactic::Rule(idx)];
                    let new_goal_stack = self.goal_stack + seq![new_goal];
                    let new_goal_traces = self.goal_traces + seq![new_trace];

                    SpecSolver {
                        goal_stack: new_goal_stack,
                        goal_traces: new_goal_traces,
                        ..self
                    }
                }
            };

            next_state.apply_all_rules(goal, trace, idx - 1)
        }
    }

    proof fn spec_apply_all_rules(self, goal: SpecGoal, trace: Seq<SpecTactic>, idx: int)
        requires
            self.inv() &&
            goal.wf() &&
            !goal.is_final() &&
            idx < self.program.rules.len() &&
            self.init_goal.reach(self.program, trace, goal)
    
        ensures ({
            let next = self.apply_all_rules(goal, trace, idx);
            next.inv()
        })

        decreases idx + 1
    {
        broadcast use SpecGoal::axiom_step;

        if idx >= 0 {
            let rule = self.program.rules[idx];
            let rule_vars = rule.free_vars();

            let first_subgoal = goal.subgoals[0];
            let goal_vars = goal.free_vars();

            // Rename overlapping variables in the goal
            let renaming = Self::gen_fresh_vars(rule_vars, goal_vars);
            let renamed_goal = goal.subst(renaming);

            // TODO
            Self::spec_gen_fresh_vars(rule_vars, goal_vars);
            assume(rule.free_vars().disjoint(renamed_goal.free_vars()));
            assume(renamed_goal.wf());

            match Self::apply_rule(self.program, renamed_goal, idx) {
                None => self.spec_apply_all_rules(goal, trace, idx - 1),
                Some(new_goal) => {
                    let new_trace = trace + seq![SpecTactic::Rename(renaming), SpecTactic::Rule(idx)];
                    let new_goal_stack = self.goal_stack + seq![new_goal];
                    let new_goal_traces = self.goal_traces + seq![new_trace];

                    let next_state = SpecSolver {
                        goal_stack: new_goal_stack,
                        goal_traces: new_goal_traces,
                        ..self
                    };

                    Self::spec_apply_rule(self.program, renamed_goal, idx);

                    // init_goal => renamed_goal
                    assert(self.init_goal.reach(self.program, trace + seq![SpecTactic::Rename(renaming)], renamed_goal)) by {
                        assert(self.init_goal.reach(self.program, trace, goal));
                        assert(goal.step(self.program, SpecTactic::Rename(renaming), renamed_goal));
                        self.init_goal.lemma_reach_append_next(self.program, trace, goal, SpecTactic::Rename(renaming), renamed_goal);
                    }

                    // init_goal => new_goal
                    assert(self.init_goal.reach(self.program, new_trace, new_goal)) by {
                        assert(renamed_goal.step(self.program, SpecTactic::Rule(idx), new_goal));
                        self.init_goal.lemma_reach_append_next(self.program, trace + seq![SpecTactic::Rename(renaming)], renamed_goal, SpecTactic::Rule(idx), new_goal);
                        assert((trace + seq![SpecTactic::Rename(renaming)]) + seq![SpecTactic::Rule(idx)] =~= new_trace);
                    }

                    next_state.spec_apply_all_rules(goal, trace, idx - 1);
                }
            }
        }
    }

    /**
     * Assume the existence of a unification algorithm
     */
    spec fn unify(t1: SpecTerm, t2: SpecTerm) -> Option<SpecSubst>;

    #[verifier::external_body]
    broadcast proof fn spec_unify(t1: SpecTerm, t2: SpecTerm)
        ensures match #[trigger] Self::unify(t1, t2) {
            Some(subst) => subst.is_mgu(t1, t2),
            None => forall |s: SpecSubst| ! #[trigger] s.is_unifier(t1, t2),
        }
    {}

    /**
     * Apply one rule to a goal using the unification algorithm
     */
    spec fn apply_rule(program: SpecProgram, goal: SpecGoal, rule_idx: int) -> Option<SpecGoal>
    {
        let first = goal.subgoals[0];
        let rule = program.rules[rule_idx];

        match Self::unify(rule.head, first) {
            Some(unifier) => {
                Some(SpecGoal {
                    subst: unifier.compose(goal.subst),
                    subgoals: (rule.body + goal.subgoals.drop_first()).map_values(|t: SpecTerm| t.subst(unifier)),
                })
            }
            None => None
        }
    }

    proof fn spec_apply_rule(program: SpecProgram, goal: SpecGoal, rule_idx: int)
        requires
            goal.wf() &&
            !goal.is_final() &&
            0 <= rule_idx < program.rules.len() &&
            program.rules[rule_idx].free_vars().disjoint(goal.free_vars())

        ensures match Self::apply_rule(program, goal, rule_idx) {
            Some(next) => goal.step(program, SpecTactic::Rule(rule_idx), next),
            None => !exists |next: SpecGoal| goal.step(program, SpecTactic::Rule(rule_idx), next),
        }
    {
        broadcast use SpecGoal::axiom_step;
        broadcast use SpecSolver::spec_unify;
    }
}

}
