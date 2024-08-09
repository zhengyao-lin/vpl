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
#[derive(Debug)]
pub struct Event {
    pub id: EventId,
    pub term: Term,
    pub tactic: Tactic,
}

#[derive(Debug)]
pub enum Tactic {
    Apply { rule_id: RuleId, subproof_ids: Vec<EventId> },
    AndIntro(EventId, EventId),
    OrIntroLeft(EventId),
    OrIntroRight(EventId),
    ForallMember { subproof_ids: Vec<EventId> },
    BuiltIn,
}

#[derive(Debug)]
pub struct TraceError(pub EventId, pub String);

/**
 * TraceValidator dynamically reads in events and construct a Theorem for each event
 * and also stores the theorem for future rule applications
 * 
 * TODO: all proofs should have unique parents, so we can probably remove theorems
 * once they are used
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

            (TermX::Literal(l1), TermX::Literal(l2)) => {
                if !l1.eq(l2) {
                    Err("unmatched literals".to_string())
                } else {
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
    pub fn process_event(&mut self, program: &Program, event: &Event, debug: bool) -> (res: Result<&Theorem, TraceError>)
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
            // Try to convert the event to a theorem via Theorem::apply_rule
            Tactic::Apply { rule_id, subproof_ids } => {
                if *rule_id >= program.rules.len() {
                    return Err(TraceError(event.id, "rule does not exist".to_string()));
                }

                let rule = &program.rules[*rule_id];

                if subproof_ids.len() != rule.body.len() {
                    return Err(TraceError(event.id, "incorrect rule application".to_string()));
                }

                if debug {
                    print("[debug] applying rule: "); println(rule);
                }

                // Figure out the substitution for the rule application
                let mut subst = Subst::new();
                let mut subproofs: Vec<&Theorem> = vec![];

                // Match rule head against goal first
                if let Err(err) = TraceValidator::match_terms(&mut subst, &rule.head, &event.term) {
                    return Err(TraceError(event.id, err));
                }
            
                // Match each rule body against existing subproof
                for i in 0..subproof_ids.len()
                    invariant
                        0 <= i <= subproof_ids.len() &&
                        subproof_ids.len() == rule.body.len() &&

                        // Invariants to show that subproofs are valid
                        subproofs.len() == i &&
                        self.wf(program@) &&
                        (forall |j| 0 <= j < i ==> (#[trigger] subproofs[j]).wf(program@))
                {
                    let subproof_id = subproof_ids[i];
                    if subproof_id >= self.thms.len() {
                        return Err(TraceError(event.id, "subproof does not exist".to_string()));
                    }
                    subproofs.push(&self.thms[subproof_id]);
                    
                    if debug {
                        print("[debug]   with subproof: "); println(&self.thms[subproof_id].stmt);
                    }

                    if let Err(err) = TraceValidator::match_terms(&mut subst, &rule.body[i], &self.thms[subproof_id].stmt) {
                        return Err(TraceError(event.id, err));
                    }
                }

                if debug {
                    print("[debug] matching substitution: "); println(&subst);
                }

                // Apply and proof-check the final result 
                if let Some(thm) = Theorem::apply_rule(program, *rule_id, &subst, subproofs) {
                    // TODO: this should be guaranteed if the matching algorithm is correct
                    // prove more about matching to conclude this without the dynamic check.
                    if (&thm.stmt).eq(&event.term) {
                        self.thms.push(thm);
                        Ok(&self.thms[event.id])
                    } else {
                        Err(TraceError(event.id, "incorrect matching algorithm".to_string()))
                    }
                } else {
                    Err(TraceError(event.id, "failed to verify proof".to_string()))
                }
            }

            Tactic::AndIntro(left_id, right_id) => {
                if *left_id >= self.thms.len() {
                    return Err(TraceError(event.id, "left subproof does not exist".to_string()));
                }

                if *right_id >= self.thms.len() {
                    return Err(TraceError(event.id, "right subproof does not exist".to_string()));
                }

                let thm = Theorem::and_intro(program, &self.thms[*left_id], &self.thms[*right_id]);

                // Check if the statement is consistent with the statement in the trace event
                if (&thm.stmt).eq(&event.term) {
                    self.thms.push(thm);
                    Ok(&self.thms[event.id])
                } else {
                    Err(TraceError(event.id, "incorrect matching algorithm".to_string()))
                }
            }

            Tactic::OrIntroLeft(subproof_id) => {
                if *subproof_id >= self.thms.len() {
                    return Err(TraceError(event.id, "subproof does not exist".to_string()));
                }

                match rc_as_ref(&event.term) {
                    TermX::App(f, args) if f.eq(&FnName::user(FN_NAME_OR, 2)) && args.len() == 2 => {
                        let thm = Theorem::or_intro_left(program, &self.thms[*subproof_id], &args[1]);

                        if (&thm.stmt).eq(&event.term) {
                            self.thms.push(thm);
                            Ok(&self.thms[event.id])
                        } else {
                            Err(TraceError(event.id, "incorrect matching algorithm".to_string()))
                        }
                    }

                    _ => Err(TraceError(event.id, "incorrect goal".to_string())),
                }
            }

            Tactic::OrIntroRight(subproof_id) => {
                if *subproof_id >= self.thms.len() {
                    return Err(TraceError(event.id, "subproof does not exist".to_string()));
                }

                match rc_as_ref(&event.term) {
                    TermX::App(f, args) if f.eq(&FnName::user(FN_NAME_OR, 2)) && args.len() == 2 => {
                        let thm = Theorem::or_intro_right(program, &args[0], &self.thms[*subproof_id]);

                        if (&thm.stmt).eq(&event.term) {
                            self.thms.push(thm);
                            Ok(&self.thms[event.id])
                        } else {
                            Err(TraceError(event.id, "incorrect matching algorithm".to_string()))
                        }
                    }

                    _ => Err(TraceError(event.id, "incorrect goal".to_string())),
                }
            }

            Tactic::ForallMember { subproof_ids } => {
                let mut subproofs: Vec<&Theorem> = vec![];

                // Collect all subproofs via the ids
                for i in 0..subproof_ids.len()
                    invariant
                        0 <= i <= subproof_ids.len() &&
                        subproofs.len() == i &&
                        self.wf(program@) &&
                        (forall |j| 0 <= j < i ==> (#[trigger] subproofs[j]).wf(program@))
                {
                    let subproof_id = subproof_ids[i];
                    if subproof_id >= self.thms.len() {
                        return Err(TraceError(event.id, "subproof does not exist".to_string()));
                    }
                    subproofs.push(&self.thms[subproof_id]);
                }

                if debug {
                    print("[debug] apply forall_member: "); println(&event.term);
                }

                if let Some(thm) = Theorem::forall_member(program, &event.term, subproofs) {
                    self.thms.push(thm);
                    Ok(&self.thms[event.id])
                } else {
                    Err(TraceError(event.id, "failed to verify proof".to_string()))
                }
            }

            Tactic::BuiltIn => {
                if let TermX::App(FnName::User(name, arity), args) = rc_as_ref(&event.term) {
                    if *arity != args.len() {
                        return Err(TraceError(event.id, "incorrect unmatched arity".to_string()));
                    }

                    if let Some(thm) = Theorem::try_domain(program, &event.term) {
                        if (&thm.stmt).eq(&event.term) {
                            self.thms.push(thm);
                            return Ok(&self.thms[event.id]);
                        } else {
                            return Err(TraceError(event.id, "incorrect matching algorithm".to_string()));
                        }
                    } else {
                        return Err(TraceError(event.id, "unsupported or unable to check built-in".to_string()));
                    }
                }

                Err(TraceError(event.id, "unsupported built-in".to_string()))
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
            tactic: Tactic::Apply { rule_id: 0, subproof_ids: vec![] },
        },
        Event {
            id: 1,
            term: TermX::app_str("edge", vec![ TermX::constant("b"), TermX::constant("c") ]),
            tactic: Tactic::Apply { rule_id: 1, subproof_ids: vec![] },
        },
        Event {
            id: 2,
            term: TermX::app_str("connect", vec![ TermX::constant("b"), TermX::constant("c") ]),
            tactic: Tactic::Apply { rule_id: 2, subproof_ids: vec![1] },
        },
        Event {
            id: 3,
            term: TermX::app_str("connect", vec![ TermX::constant("a"), TermX::constant("c") ]),
            tactic: Tactic::Apply { rule_id: 3, subproof_ids: vec![0, 2] },
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
        match validator.process_event(&program, &events[i], true) {
            Ok(thm) => {
                assert(thm.wf(program@));
                print("Event "); print(events[i].id); print(" verified: "); println(&thm.stmt);
            }
            Err(msg) => {
                print("Event "); print(events[i].id); print(" failed: "); println_debug(msg);
                break;
            }
        }
        i += 1;
    }
}

}
