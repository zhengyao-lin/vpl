use vstd::prelude::*;

use crate::checker::*;
use crate::polyfill::*;

// A naive (and incomplete) Prolog solver

verus! {

impl Subst {
    #[verifier::external_body]
    pub fn compose(&self, mut other: &Subst) -> Subst {
        let mut new_subst = other.clone();
        for var in other.0.m.keys() {
            let new_term = TermX::subst(other.0.get(var).unwrap(), self);
            new_subst.0.insert(var.clone(), new_term);
        }
        for var in self.0.m.keys() {
            if !new_subst.0.contains_key(var) {
                new_subst.0.insert(var.clone(), self.0.get(var).unwrap().clone());
            }
        }
        new_subst
    }
}

/// A naive implementation of unification
/// TODO: tidy this up
pub fn unify(t1: &Term, t2: &Term) -> Option<Subst>
{
    let mut subst = Subst::new();
    let mut eq_left = vec![t1.clone()];
    let mut eq_right = vec![t2.clone()];

    loop
        invariant eq_left.len() == eq_right.len()
    {
        if let (Some(t1), Some(t2)) = (eq_left.pop(), eq_right.pop()) {
            if (&t1).eq(&t2) {
                continue;
            }

            match (rc_as_ref(&t1), rc_as_ref(&t2)) {
                (TermX::Var(v1), _) => {
                    // TODO: check if v occurs in t
                    let mut v_to_t = Subst::new();
                    v_to_t.insert(v1.clone(), t2.clone());

                    let mut i = 0;
                    let eq_len = eq_left.len();

                    while i < eq_len
                        invariant
                            eq_left.len() == eq_len &&
                            eq_right.len() == eq_len
                    {
                        let left = TermX::subst(&eq_left[i], &v_to_t);
                        let right = TermX::subst(&eq_right[i], &v_to_t);
                        vec_set(&mut eq_left, i, left);
                        vec_set(&mut eq_right, i, right);
                        i += 1;
                    }

                    subst.insert(v1.clone(), t2.clone());
                }
                (_, TermX::Var(_)) => {
                    eq_left.push(t2);
                    eq_right.push(t1);
                }
                (TermX::App(f1, args1), TermX::App(f2, args2)) => {
                    if f1.eq(f2) && args1.len() == args2.len() {
                        for i in 0..args1.len()
                            invariant
                                args1.len() == args2.len() &&
                                eq_left.len() == eq_right.len()
                        {
                            eq_left.push(args1[i].clone());
                            eq_right.push(args2[i].clone());
                        }
                    } else {
                        return None;
                    }
                },
            }
        } else {
            break;
        }
    }

    Some(subst)
}

#[derive(Clone)]
pub struct Solution {
    subst: Subst,
    proof: Theorem,
}

pub struct Solver {
    goal: Term,
    cur_solution: Option<Solution>, // latest solution found

    cur_rule_id: RuleId,
    unifier: Option<Subst>, // unifier for the current rule
    subgoals: Vec<Term>, // subgoals after applied the current rule
    subgoal_solvers: Vec<Solver>,
}

impl Solver {
    pub fn new(goal: Term) -> Solver {
        Solver {
            goal: goal,
            cur_solution: None,

            cur_rule_id: 0,
            unifier: None,
            subgoals: vec![],
            subgoal_solvers: vec![],
        }
    }

    #[verifier::external_body]
    pub fn next(&mut self, program: &Program) -> Result<Option<Solution>, String> {
        'outer: while self.cur_rule_id < program.rules.len() {
            // Get the current unifier
            let unifier = match &self.unifier {
                Some(unifier) => unifier,
                None => {
                    // Haven't applied the current rule yet
                    let rule = &program.rules[self.cur_rule_id];

                    // TODO: rename variables

                    if let Some(unifier) = unify(&rule.head, &self.goal) {
                        // Initialize self.subgoals to the instances of the rule body
                        let mut subgoals = vec![];
                        for i in 0..rule.body.len() {
                            subgoals.push(TermX::subst(&rule.body[i], &unifier));
                        }
                        self.subgoals = subgoals;
                        self.unifier = Some(unifier);
                        self.unifier.as_ref().unwrap()
                    } else {
                        // The current rule doesn't apply
                        // Try the next one
                        self.cur_rule_id += 1;
                        continue;
                    }
                }
            };

            // Start searching for the next solution
            let mut cur_subgoal_idx = if self.subgoal_solvers.len() > 0 {
                self.subgoal_solvers.len() - 1
            } else {
                0
            };

            // Backtracking loop
            while cur_subgoal_idx < self.subgoals.len() {
                if cur_subgoal_idx >= self.subgoal_solvers.len() {
                    // A new subgoal that doesn't have a corresponding solver

                    // Apply all substitutions from the solutions
                    // of previous obligations to get the next subgoal
                    let mut subgoal = self.subgoals[cur_subgoal_idx].clone();
                    for j in 0..self.subgoal_solvers.len() {
                        let prev_subst = &self.subgoal_solvers[j].cur_solution.as_ref().unwrap().subst;
                        subgoal = TermX::subst(&subgoal, prev_subst);
                    }

                    // Generate a solver for the next subgoal
                    self.subgoal_solvers.push(Solver::new(subgoal));
                }

                let solver = &mut self.subgoal_solvers[cur_subgoal_idx];

                if let Some(solution) = solver.next(program)? {
                    // If this is the last subgoal, finish backtracking
                    if cur_subgoal_idx == self.subgoals.len() - 1 {
                        break;
                    }

                    // Otherwise move on to the next subgoal
                    cur_subgoal_idx += 1;
                } else {
                    self.subgoal_solvers.pop();
                    if cur_subgoal_idx == 0 {
                        // Exhausted even the first subgoal, try next rule
                        self.cur_rule_id += 1;
                        self.unifier = None;
                        continue 'outer;
                    } else {
                        // No more solutions possible at an intermediate subgoal, backtrack
                        cur_subgoal_idx -= 1;
                        // println!("backtrack at subgoal {}", cur_subgoal_idx);
                    }
                }
            }

            // Found the next solution, build a theorem
            let mut solution_subst = unifier.clone();
            let mut subproofs = vec![];

            // println!("subst: {:?}", &solution_subst);
            for j in 0..self.subgoal_solvers.len() {
                // println!("subst: {:?}", &self.subgoal_solvers[j].subst);
                let cur_solution = self.subgoal_solvers[j].cur_solution.as_ref().unwrap();
                solution_subst = cur_solution.subst.compose(&solution_subst);
                subproofs.push(&cur_solution.proof);
            }

            if let Some(thm) = Theorem::apply_rule(program, self.cur_rule_id, &solution_subst, subproofs) {
                let solution = Solution {
                    subst: solution_subst,
                    proof: thm,
                };

                if self.subgoals.len() == 0 {
                    // If this is a fact, then no more solutions are possible
                    self.cur_rule_id += 1;
                    self.unifier = None;
                }

                self.cur_solution = Some(solution.clone());

                return Ok(Some(solution));
            } else {
                return Err(format!("proof check failed"));
            }
        }

        Ok(None)
    }
}

#[verifier::external_body]
pub fn test() {
    // connectivity11.pl
    let program = ProgramX::new(vec![
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n66"), TermX::constant("n96") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n23"), TermX::constant("n59") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n49"), TermX::constant("n50") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n26"), TermX::constant("n27") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n15"), TermX::constant("n16") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n24"), TermX::constant("n25") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n11"), TermX::constant("n12") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n10"), TermX::constant("n11") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n32"), TermX::constant("n33") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n23"), TermX::constant("n24") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n64"), TermX::constant("n74") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n27"), TermX::constant("n51") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n34"), TermX::constant("n35") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n16"), TermX::constant("n85") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n17"), TermX::constant("n62") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n17"), TermX::constant("n18") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n40"), TermX::constant("n41") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n22"), TermX::constant("n23") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n18"), TermX::constant("n69") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n9"), TermX::constant("n88") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n48"), TermX::constant("n77") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n3"), TermX::constant("n4") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n39"), TermX::constant("n40") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n41"), TermX::constant("n42") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n6"), TermX::constant("n7") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n21"), TermX::constant("n22") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n18"), TermX::constant("n19") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n11"), TermX::constant("n97") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n76"), TermX::constant("n92") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n10"), TermX::constant("n67") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n45"), TermX::constant("n72") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n7"), TermX::constant("n8") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n46"), TermX::constant("n84") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n5"), TermX::constant("n58") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n31"), TermX::constant("n32") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n41"), TermX::constant("n100") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n1"), TermX::constant("n70") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n80"), TermX::constant("n90") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n13"), TermX::constant("n78") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n28"), TermX::constant("n29") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n9"), TermX::constant("n87") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n68"), TermX::constant("n71") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n18"), TermX::constant("n55") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n40"), TermX::constant("n56") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n57"), TermX::constant("n75") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n59"), TermX::constant("n83") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n35"), TermX::constant("n36") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n45"), TermX::constant("n46") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n36"), TermX::constant("n37") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n38"), TermX::constant("n39") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n43"), TermX::constant("n44") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n30"), TermX::constant("n64") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n5"), TermX::constant("n6") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n60"), TermX::constant("n95") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n2"), TermX::constant("n3") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n41"), TermX::constant("n93") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n48"), TermX::constant("n49") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n1"), TermX::constant("n2") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n11"), TermX::constant("n52") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n27"), TermX::constant("n28") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n16"), TermX::constant("n17") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n20"), TermX::constant("n57") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n86"), TermX::constant("n89") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n64"), TermX::constant("n66") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n4"), TermX::constant("n5") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n36"), TermX::constant("n68") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n65"), TermX::constant("n91") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n62"), TermX::constant("n86") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n20"), TermX::constant("n21") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n47"), TermX::constant("n73") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n21"), TermX::constant("n81") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n56"), TermX::constant("n63") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n37"), TermX::constant("n38") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n72"), TermX::constant("n94") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n9"), TermX::constant("n10") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n43"), TermX::constant("n61") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n16"), TermX::constant("n99") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n19"), TermX::constant("n20") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n50"), TermX::constant("n98") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n47"), TermX::constant("n48") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n13"), TermX::constant("n14") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n16"), TermX::constant("n60") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n46"), TermX::constant("n82") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n44"), TermX::constant("n45") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n30"), TermX::constant("n31") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n40"), TermX::constant("n76") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n14"), TermX::constant("n15") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n29"), TermX::constant("n30") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n46"), TermX::constant("n47") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n13"), TermX::constant("n53") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n8"), TermX::constant("n9") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n52"), TermX::constant("n80") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n8"), TermX::constant("n65") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n6"), TermX::constant("n79") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n12"), TermX::constant("n13") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n35"), TermX::constant("n54") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n25"), TermX::constant("n26") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n0"), TermX::constant("n1") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n42"), TermX::constant("n43") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n33"), TermX::constant("n34") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("a"), TermX::constant("b") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("b"), TermX::constant("c") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("c"), TermX::constant("a") ]), vec![]),
        RuleX::new(TermX::app_str("connect", vec![ TermX::var_str("X"), TermX::var_str("Y") ]), vec![
            TermX::app_str("edge", vec![ TermX::var_str("X"), TermX::var_str("Y") ]),
        ]),
        RuleX::new(TermX::app_str("connect", vec![ TermX::var_str("X"), TermX::var_str("Z") ]), vec![
            TermX::app_str("edge", vec![ TermX::var_str("X"), TermX::var_str("Y") ]),
            TermX::app_str("connect", vec![ TermX::var_str("Y"), TermX::var_str("Z") ]),
        ]),
    ]);

    let goal = TermX::app_str("connect", vec![ TermX::var_str("_X"), TermX::var_str("_Y") ]);

    let mut solver = Solver::new(goal);

    loop {
        match solver.next(&program) {
            Ok(Some(solution)) => {
                println!("found solution: {:?} {:?}", solution.proof.stmt, solution.subst);
            },
            Ok(None) => {
                println!("no more solutions");
                break;
            },
            Err(msg) => {
                println!("error: {}", msg);
                break;
            },
        }
    }
}

}
