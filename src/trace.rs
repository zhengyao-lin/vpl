use vstd::prelude::*;

use crate::proof::*;
use crate::checker::*;
use crate::polyfill::*;

// Checks the proofs as traces from an on-the-shelf Prolog solver
// Traces = Hilbert-style proofs with less details

verus! {

broadcast use TermX::axiom_view, SpecTerm::axiom_subst;

pub type EventId = usize;

/**
 * A trace is a sequence of events of the form
 *   <id> <term> by <tactic>
 * where
 * - <id> is the unique id of the event,
 * - <term> is the goal proved, and
 * - <tactic> is the tactic applied to get here.
 */
pub struct Event {
    pub id: EventId,
    pub term: Term,
    pub tactic: Tactic,
}

pub enum Tactic {
    Apply { rule_idx: RuleId, subproof_ids: Vec<EventId> },
    BuiltIn,
}

/**
 * TraceValidator dynamically reads in events and construct a Theorem for each event
 * and also stores the theorem for future rule applications
 */
pub struct TraceValidator {
    pub thms: Vec<Theorem>,
}

impl TraceValidator {
    pub fn new(program: &Program) -> (res: Self)
        ensures res.wf(program@) && res.thms.len() == 0
    {
        Self { thms: Vec::new() }
    }

    pub open spec fn wf(self, program: SpecProgram) -> bool {
        forall |i| 0 <= i < self.thms.len() ==> (#[trigger] self.thms[i]).wf(program)
    }

    // pub closed spec fn match_terms_trigger(subst: &Subst, term1: SpecTerm, term2: SpecTerm);

    /**
     * Perform matching of pattern against inst
     * only set variables in pattern
     * 
     * Store new substitutions in subst, fail if a key already exists
     * and has an inconsistent value
     */
    pub fn match_terms(subst: &mut Subst, pattern: &Term, inst: &Term) -> (res: Result<(), String>)
        // ensures res matches Ok(_) ==> pattern@.subst(subst@) == inst@
    {
        match (rc_as_ref(pattern), rc_as_ref(inst)) {
            (TermX::Var(var), _) => {
                if let Some(existing) = subst.get(var) {
                    if !existing.eq(inst) {
                        Err("inconsistent substitution".to_string())
                    } else {
                        Ok(())
                    }
                } else {
                    subst.insert(var.clone(), inst.clone());
                    Ok(())
                }
            }

            (TermX::App(f1, args1), TermX::App(f2, args2)) => {
                if !f1.eq(f2) {
                    return Err("unmatched function symbol".to_string());
                }

                if args1.len() != args2.len() {
                    return Err("unmatched argument length".to_string());
                }

                // Match each subterm
                for i in 0..args1.len()
                    invariant
                        0 <= i <= args1.len() &&
                        args1.len() == args2.len()
                {
                    TraceValidator::match_terms(subst, &args1[i], &args2[i])?;
                }

                Ok(())
            }

            _ => Err("unmatched terms".to_string()),
        }
    }

    /// Process an event and construct a Theorem with the same statement claimed in the event
    /// Retuen the Theorem object if successful
    pub fn process_event(&mut self, program: &Program, event: &Event) -> (res: Result<&Theorem, String>)
        requires
            old(self).wf(program@) &&

            // For simplicity, we assume that the event id coincides with the index of the event
            event.id == old(self).thms.len()

        ensures
            res matches Ok(thm) ==> (
                self.wf(program@) &&
                thm.wf(program@) &&
                
                self.thms[event.id as int].stmt@ == event.term@ &&
                event.term@ == thm.stmt@ &&
            
                // self.thms has exact one more element
                self.thms.len() == old(self).thms.len() + 1 &&
                (forall |i| 0 <= i < old(self).thms.len() ==> old(self).thms[i] == self.thms[i])
            )
    {
        match &event.tactic {
            Tactic::BuiltIn => Err("not implemented".to_string()),

            Tactic::Apply { rule_idx, subproof_ids } => {
                if *rule_idx >= program.rules.len() {
                    return Err("rule does not exist".to_string());
                }

                let rule = &program.rules[*rule_idx];

                if subproof_ids.len() != rule.body.len() {
                    return Err("incorrect rule application".to_string());
                }

                // Figure out the substitution for the rule application
                let mut subst = Subst::new();
                let mut subproofs: Vec<&Theorem> = vec![];

                // Match rule head against goal first
                TraceValidator::match_terms(&mut subst, &rule.head, &event.term)?;
            
                // Match each rule body against existing subproof
                for i in 0..subproof_ids.len()
                    invariant
                        0 <= i <= subproof_ids.len() &&
                        subproof_ids.len() == rule.body.len() &&

                        // Invariants to show that subproofs are valid
                        subproofs.len() == i &&
                        (forall |j| 0 <= j < self.thms.len() ==> (#[trigger] self.thms[j]).wf(program@)) &&
                        (forall |j| 0 <= j < i ==> (#[trigger] subproofs[j]).wf(program@))
                {
                    let subproof_id = subproof_ids[i];
                    if subproof_id >= self.thms.len() {
                        return Err("subproof does not exist".to_string());
                    }
                    subproofs.push(&self.thms[subproof_id]);
                    TraceValidator::match_terms(&mut subst, &rule.body[i], &self.thms[subproof_id].stmt)?;
                }

                // Apply and proof-check the final result 
                if let Some(thm) = Theorem::apply_rule(program, *rule_idx, &subst, subproofs) {
                    // TODO: this should be guaranteed if the matching algorithm is correct
                    // prove more about matching to conclude this without the dynamic check.
                    if (&thm.stmt).eq(&event.term) {
                        self.thms.push(thm);
                        Ok(&self.thms[event.id])
                    } else {
                        Err("incorrect matching algorithm".to_string())
                    }
                } else {
                    Err("failed to verify proof".to_string())
                }
            }
        }
    }
}

pub fn test() {
    let program = ProgramX::new(vec![
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("a"), TermX::constant("b") ]), vec![]),
        RuleX::new(TermX::app_str("edge", vec![ TermX::constant("b"), TermX::constant("c") ]), vec![]),
        RuleX::new(TermX::app_str("connect", vec![ TermX::var_str("X"), TermX::var_str("Y") ]), vec![
            TermX::app_str("edge", vec![ TermX::var_str("X"), TermX::var_str("Y") ]),
        ]),
        RuleX::new(TermX::app_str("connect", vec![ TermX::var_str("X"), TermX::var_str("Z") ]), vec![
            TermX::app_str("edge", vec![ TermX::var_str("X"), TermX::var_str("Y") ]),
            TermX::app_str("connect", vec![ TermX::var_str("Y"), TermX::var_str("Z") ]),
        ]),
    ]);

    let goal = TermX::app_str("connect", vec![ TermX::var_str("a"), TermX::var_str("b") ]);

    let mut validator = TraceValidator::new(&program);

    let events = vec![
        Event {
            id: 0,
            term: TermX::app_str("edge", vec![ TermX::constant("a"), TermX::constant("b") ]),
            tactic: Tactic::Apply { rule_idx: 0, subproof_ids: vec![] },
        },
        Event {
            id: 1,
            term: TermX::app_str("edge", vec![ TermX::constant("b"), TermX::constant("c") ]),
            tactic: Tactic::Apply { rule_idx: 1, subproof_ids: vec![] },
        },
        Event {
            id: 2,
            term: TermX::app_str("connect", vec![ TermX::constant("b"), TermX::constant("c") ]),
            tactic: Tactic::Apply { rule_idx: 2, subproof_ids: vec![1] },
        },
        Event {
            id: 3,
            term: TermX::app_str("connect", vec![ TermX::constant("a"), TermX::constant("c") ]),
            tactic: Tactic::Apply { rule_idx: 3, subproof_ids: vec![0, 2] },
        },
    ];

    let mut i = 0;

    while i < events.len()
        invariant_except_break
            0 <= i <= events.len() &&
            validator.wf(program@) &&
            validator.thms.len() == i &&
            (forall |i: int| 0 <= i < events.len() ==> (#[trigger] events[i].id) as int == i)
    {
        match validator.process_event(&program, &events[i]) {
            Ok(thm) => {
                assert(thm.wf(program@));
                print("Event "); print(events[i].id); print(" verified: "); println(&thm.stmt);
            }
            Err(msg) => {
                print("Event "); print(events[i].id); print(" failed: "); println(msg);
                break;
            }
        }
        i += 1;
    }
}

}
