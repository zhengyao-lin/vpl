mod proof;
mod checker;
mod containers;
mod view;
mod polyfill;

use vstd::prelude::*;

use std::cell::Cell;

use crate::containers::StringHashMap;
use crate::checker::*;
use crate::polyfill::*;

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

#[verifier::external_body]
pub fn vec_set<T>(v: &mut Vec<T>, i: usize, x: T)
    requires 0 <= i < old(v).len()
    ensures
        v.len() == old(v).len() &&
        (forall |j| 0 <= j < v.len() && j != i ==> v[j] == old(v)[j]) &&
        v[i as int] == x
{
    v[i] = x;
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
                (_, TermX::Var(v2)) => {
                    // TODO: check if v occurs in t
                    let mut v_to_t = Subst::new();
                    v_to_t.insert(v2.clone(), t1.clone());

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

                    subst.insert(v2.clone(), t1.clone());
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

// At each goal
// for i in 0..rule
//    apply rule i to goal to get subgoals
//    for each subgoal
//        generate a solver object
//    for solution in subgoal1
//        for solution in subgoal2
//             ...
//             for solution in subgoal_last
//                   output combined solution

/// A naive proof search procedure for Prolog
#[verifier::external_body]
pub fn proof_search(program: &Program, goal: &Term) -> (res: Result<Option<(Subst, Theorem)>, String>)
    ensures
        res matches Ok(Some((_, thm))) ==> thm.inv(program@)
{
    for i in 0..program.rules.len() {
        let rule = &program.rules[i];

        println!("goal {:?}, trying rule {}", goal, i);

        if let Some(mut subst) = unify(&rule.head, goal) {
            let mut success = true;
            let mut subproofs: Vec<Theorem> = Vec::new();
            let mut j = 0;

            let mut subgoals = rule.body.clone();
            let num_subgoals = subgoals.len();
            
            while j < num_subgoals
                invariant
                    subgoals.len() == num_subgoals &&
                    (forall |k| 0 <= k < subproofs.len() ==> (#[trigger] subproofs[k]).inv(program@))
            {
                let mut next_subgoal = TermX::subst(&subgoals[j], &subst);
                
                // TODO: Need to backtrack here!
                if let Some((sub_subst, thm)) = proof_search(program, &next_subgoal)? {
                    subproofs.push(thm);
                    subst = sub_subst.compose(&subst);

                    // // Apply the result substitution to each of the remaining subgoals
                    // let mut k = j;
                    // while k < num_subgoals
                    //     invariant
                    //         subgoals.len() == num_subgoals
                    // {
                    //     let new_subgoal = TermX::subst(&subgoals[k], &sub_subst);
                    //     vec_set(&mut subgoals, k, new_subgoal);
                    //     k += 1;
                    // }

                    j += 1;
                } else {
                    success = false;
                    break;
                }
            }

            if success {
                if let Some(thm) = Theorem::apply_rule(program, i, &subst, subproofs) {
                    println!("success {:?} {:?}", goal, subst);
                    return Ok(Some((subst, thm)));
                } else {
                    return Err("proof check failed".to_string());
                }
            }
        }
    }

    Ok(None)
}

}

pub fn main() {
    // connectivity11.pl
    let program = ProgramX::new(vec![
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n66"), TermX::constant("n96") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n23"), TermX::constant("n59") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n49"), TermX::constant("n50") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n26"), TermX::constant("n27") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n15"), TermX::constant("n16") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n24"), TermX::constant("n25") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n11"), TermX::constant("n12") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n10"), TermX::constant("n11") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n32"), TermX::constant("n33") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n23"), TermX::constant("n24") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n64"), TermX::constant("n74") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n27"), TermX::constant("n51") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n34"), TermX::constant("n35") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n16"), TermX::constant("n85") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n17"), TermX::constant("n62") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n17"), TermX::constant("n18") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n40"), TermX::constant("n41") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n22"), TermX::constant("n23") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n18"), TermX::constant("n69") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n9"), TermX::constant("n88") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n48"), TermX::constant("n77") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n3"), TermX::constant("n4") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n39"), TermX::constant("n40") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n41"), TermX::constant("n42") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n6"), TermX::constant("n7") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n21"), TermX::constant("n22") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n18"), TermX::constant("n19") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n11"), TermX::constant("n97") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n76"), TermX::constant("n92") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n10"), TermX::constant("n67") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n45"), TermX::constant("n72") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n7"), TermX::constant("n8") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n46"), TermX::constant("n84") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n5"), TermX::constant("n58") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n31"), TermX::constant("n32") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n41"), TermX::constant("n100") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n1"), TermX::constant("n70") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n80"), TermX::constant("n90") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n13"), TermX::constant("n78") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n28"), TermX::constant("n29") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n9"), TermX::constant("n87") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n68"), TermX::constant("n71") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n18"), TermX::constant("n55") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n40"), TermX::constant("n56") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n57"), TermX::constant("n75") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n59"), TermX::constant("n83") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n35"), TermX::constant("n36") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n45"), TermX::constant("n46") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n36"), TermX::constant("n37") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n38"), TermX::constant("n39") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n43"), TermX::constant("n44") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n30"), TermX::constant("n64") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n5"), TermX::constant("n6") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n60"), TermX::constant("n95") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n2"), TermX::constant("n3") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n41"), TermX::constant("n93") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n48"), TermX::constant("n49") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n1"), TermX::constant("n2") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n11"), TermX::constant("n52") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n27"), TermX::constant("n28") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n16"), TermX::constant("n17") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n20"), TermX::constant("n57") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n86"), TermX::constant("n89") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n64"), TermX::constant("n66") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n4"), TermX::constant("n5") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n36"), TermX::constant("n68") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n65"), TermX::constant("n91") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n62"), TermX::constant("n86") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n20"), TermX::constant("n21") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n47"), TermX::constant("n73") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n21"), TermX::constant("n81") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n56"), TermX::constant("n63") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n37"), TermX::constant("n38") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n72"), TermX::constant("n94") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n9"), TermX::constant("n10") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n43"), TermX::constant("n61") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n16"), TermX::constant("n99") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n19"), TermX::constant("n20") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n50"), TermX::constant("n98") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n47"), TermX::constant("n48") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n13"), TermX::constant("n14") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n16"), TermX::constant("n60") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n46"), TermX::constant("n82") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n44"), TermX::constant("n45") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n30"), TermX::constant("n31") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n40"), TermX::constant("n76") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n14"), TermX::constant("n15") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n29"), TermX::constant("n30") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n46"), TermX::constant("n47") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n13"), TermX::constant("n53") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n8"), TermX::constant("n9") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n52"), TermX::constant("n80") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n8"), TermX::constant("n65") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n6"), TermX::constant("n79") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n12"), TermX::constant("n13") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n35"), TermX::constant("n54") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n25"), TermX::constant("n26") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n0"), TermX::constant("n1") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n42"), TermX::constant("n43") ]), vec![]),
        // RuleX::new(TermX::app_str("edge", vec![ TermX::constant("n33"), TermX::constant("n34") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("a"), TermX::constant("d") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("a"), TermX::constant("b") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("b"), TermX::constant("c") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("d"), TermX::constant("c") ]), vec![]),
        RuleX::new(TermX::app_str("connect", vec![ TermX::var_str("X"), TermX::var_str("Y") ]), vec![
            TermX::app_str("edge", vec![ TermX::var_str("X"), TermX::var_str("Y") ]),
        ]),
        RuleX::new(TermX::app_str("connect", vec![ TermX::var_str("X"), TermX::var_str("Z") ]), vec![
            TermX::app_str("edge", vec![ TermX::var_str("X"), TermX::var_str("Y") ]),
            TermX::app_str("connect", vec![ TermX::var_str("Y"), TermX::var_str("Z") ]),
        ]),
    ]);

    // let empty_subst = Subst(StringHashMap::new());
    // let mut subst1 = Subst(StringHashMap::new());
    // let mut subst2 = Subst(StringHashMap::new());

    // subst1.0.insert("X".to_string(), TermX::constant("b"));
    // subst1.0.insert("Y".to_string(), TermX::constant("c"));

    // subst2.0.insert("X".to_string(), TermX::constant("a"));
    // subst2.0.insert("Y".to_string(), TermX::constant("b"));
    // subst2.0.insert("Z".to_string(), TermX::constant("c"));
    
    // let edge_ab = Theorem::apply_rule(&program, 0, &empty_subst, vec![]);
    // let edge_bc = Theorem::apply_rule(&program, 1, &empty_subst, vec![]);

    // if let (Some(edge_ab), Some(edge_bc)) = (edge_ab, edge_bc) {
    //     if let Some(connect_bc) = Theorem::apply_rule(&program, 2, &subst1, vec![ edge_bc ]) {
    //         if let Some(connect_ac) = Theorem::apply_rule(&program, 3, &subst2, vec![ edge_ab, connect_bc ]) {
    //             println!("thm: {:?}", connect_ac.stmt);
    //         } else {
    //             println!("failed connect_ac");
    //         }
    //     } else {
    //         println!("failed connect_bc");
    //     }
    // } else {
    //     println!("failed edge");
    // }

    let goal = TermX::app_str("connect", vec![ TermX::var_str("_X"), TermX::var_str("_Y") ]);

    // match proof_search(&program, &goal) {
    //     Ok(Some((_, thm))) => {
    //         println!("proved: {:?}", thm.stmt);
    //     },
    //     Ok(None) => {
    //         println!("no proof found");
    //     },
    //     Err(msg) => {
    //         println!("error: {}", msg);
    //     },
    // }

    let mut solver = Solver::new(goal);

    loop {
        match solver.get_next(&program) {
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

pub struct Solution {
    subst: Subst,
    proof: Theorem,
}

pub struct Solver {
    goal: Term,
    cur_rule_idx: RuleId,
    
    subgoals: Option<Vec<Term>>, // subgoals after applied the current rule
    subst: Option<Subst>, // substitution after applied the current rule

    solution_stack: Vec<Solution>, // current solution at each solver
    solver_stack: Vec<Solver>,
}

impl Solver {
    pub fn new(goal: Term) -> Solver {
        Solver {
            goal: goal,
            cur_rule_idx: 0,
            subgoals: None,
            subst: None,
            solution_stack: vec![],
            solver_stack: vec![],
        }
    }

    // Some if there is a solution
    // None if no more solution can be found
    pub fn get_next(&mut self, program: &Program) -> Result<Option<Solution>, String> {
        loop {
            if self.subgoals.is_none() {
                let mut rule_idx = self.cur_rule_idx;
                let mut found = false;

                // Find the next rule that applies to self.goal
                while rule_idx < program.rules.len() {
                    let rule = &program.rules[rule_idx];

                    // TODO: generate fresh goals here
                    
                    if let Some(mut subst) = unify(&rule.head, &self.goal) {
                        // Initialize self.subgoals to the instances of the rule body
                        let mut subgoals = vec![];
                        for i in 0..rule.body.len() {
                            subgoals.push(TermX::subst(&rule.body[i], &subst));
                        }
                        self.cur_rule_idx = rule_idx;
                        self.subgoals = Some(subgoals);
                        self.subst = Some(subst);
                        found = true;
                        break;
                    } else {
                        // println!("failed to unify {:?} and {:?}", &rule.head, &self.goal);
                        rule_idx += 1;
                    }
                }

                // No more rules applies, return with no solution
                if !found {
                    // TODO: clear up the fields?
                    return Ok(None);
                }
            }

            let subgoals = self.subgoals.as_ref().unwrap();
            let subst = self.subst.as_ref().unwrap();

            // println!("applied rule {}, subgoals: {:?}", self.cur_rule_idx, subgoals);

            // The current rule is a fact
            if subgoals.len() == 0 {
                if let Some(thm) = Theorem::apply_rule(program, self.cur_rule_idx, subst, vec![]) {
                    let solution = Solution {
                        subst: subst.clone(),
                        proof: thm,
                    };
                    self.cur_rule_idx += 1;
                    self.subgoals = None;
                    self.subst = None;
                    // println!("proved: {:?}", &solution.proof.stmt);
                    return Ok(Some(solution));
                } else {
                    return Err("proof check failed base".to_string());
                }
            }

            // Start at the last solver
            let mut cur_subgoal_idx = if self.solver_stack.len() > 0 {
                self.solver_stack.len() - 1
            } else {
                0
            };

            while cur_subgoal_idx < subgoals.len() {
                // For each subgoal:
                // 1. Instantiate a solver object if not set
                // 2. Try to get the next solution

                // println!("at subgoal {}, {}, {}", cur_subgoal_idx, self.solution_stack.len(), self.solver_stack.len());

                if cur_subgoal_idx >= self.solver_stack.len() {
                    // Apply all substitutions from the solutions
                    // of previous obligations to get the next subgoal
                    let mut subgoal = subgoals[cur_subgoal_idx].clone();
                    for j in 0..self.solution_stack.len() {
                        subgoal = TermX::subst(&subgoal, &self.solution_stack[j].subst);
                    }

                    // println!("new solver for subgoal {:?}", subgoal);
                    
                    // Generate a solver for the next subgoal
                    self.solver_stack.push(Solver::new(subgoal));
                }

                let solver = &mut self.solver_stack[cur_subgoal_idx];

                if let Some(solution) = solver.get_next(program)? {
                    // Set solution
                    if cur_subgoal_idx >= self.solution_stack.len() {
                        self.solution_stack.push(solution);
                    } else {
                        self.solution_stack[cur_subgoal_idx] = solution;
                    }
                    
                    // If this is the last subgoal, return the solution
                    if cur_subgoal_idx == subgoals.len() - 1 {
                        let mut solution_subst = subst.clone();
                        // println!("subst: {:?}", &solution_subst);
                        for j in 0..self.solution_stack.len() {
                            // println!("subst: {:?}", &self.solution_stack[j].subst);
                            solution_subst = self.solution_stack[j].subst.compose(&solution_subst);
                        }

                        let mut subproofs = vec![];
                        for j in 0..self.solution_stack.len() {
                            subproofs.push(self.solution_stack[j].proof.clone());
                        }

                        if let Some(thm) = Theorem::apply_rule(program, self.cur_rule_idx, &solution_subst, subproofs) {
                            let solution = Solution {
                                subst: solution_subst,
                                proof: thm,
                            };
                            // println!("proved: {:?}", &solution.proof.stmt);
                            return Ok(Some(solution));
                        } else {
                            return Err(format!("proof check failed: {} {:?} {:?}", self.cur_rule_idx, &solution_subst, self.solution_stack.iter().map(|t| t.proof.stmt.clone()).collect::<Vec<_>>()));
                        }
                    }

                    // Move on to the next subgoal
                    cur_subgoal_idx += 1;
                } else {
                    if cur_subgoal_idx == 0 {
                        // Exhausted even the first subgoal, try next rule
                        self.cur_rule_idx += 1;
                        self.subgoals = None;
                        self.subst = None;
                        if cur_subgoal_idx < self.solution_stack.len() {
                            self.solution_stack.pop();
                        }
                        self.solver_stack.pop();
                        break;
                    } else {
                        // No more solutions possible at an intermediate subgoal, backtrack
                        self.solution_stack.pop();
                        self.solver_stack.pop();
                        cur_subgoal_idx -= 1;
                        // println!("backtrack at subgoal {}", cur_subgoal_idx);
                    }
                }
            }
        }
    }
}
