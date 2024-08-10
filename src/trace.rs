use vstd::prelude::*;
use std::collections::HashMap;

use crate::proof::*;
use crate::checker::*;
use crate::polyfill::*;

// Checks the proofs as traces from an on-the-shelf Prolog solver
// Traces = Hilbert-style proofs with less details

verus! {

broadcast use TermX::axiom_view, SpecTerm::axiom_subst, vstd::std_specs::hash::group_hash_axioms;

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
    ForallMember(Vec<EventId>),
    ForallBase(Vec<EventId>),
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
    pub thms: HashMap<EventId, Theorem>,
}

impl TraceValidator {
    pub fn new(program: &Program) -> (res: Self)
        ensures res.wf(program@) && res.thms@.len() == 0
    {
        Self { thms: HashMap::new() }
    }

    pub open spec fn wf(self, program: SpecProgram) -> bool {
        forall |id| self.thms@.contains_key(id) ==> (#[trigger] self.thms@[id]).wf(program)
    }

    // pub closed spec fn match_terms_trigger(subst: &Subst, term1: SpecTerm, term2: SpecTerm);

    pub fn add_theorem(&mut self, program: &Program, event_id: EventId, thm: Theorem) -> (res: &Theorem)
        requires old(self).wf(program@) && thm.wf(program@)
        ensures
            self.wf(program@) &&
            self.thms@.contains_key(event_id) &&
            self.thms@[event_id] == thm &&
            res == thm
    {
        self.thms.insert(event_id, thm);
        &self.thms.get(&event_id).unwrap()
    }

    pub fn get_theorem(&self, program: &Program, event_id: EventId) -> (res: Result<&Theorem, TraceError>)
        requires self.wf(program@)
        ensures res matches Ok(thm) ==> thm.wf(program@)
    {
        if let Some(thm) = self.thms.get(&event_id) {
            Ok(thm)
        } else {
            Err(TraceError(event_id, "theorem does not exist".to_string()))
        }
    }

    pub fn remove_theorem(&mut self, program: &Program, event_id: EventId) -> (res: Result<Theorem, TraceError>)
        requires old(self).wf(program@)
        ensures
            self.wf(program@) &&
            
            // Does not change other theorems
            (forall |id| id != event_id && old(self).thms@.contains_key(id) ==>
                self.thms@.contains_key(id) &&
                #[trigger] self.thms@[id] == old(self).thms@[id]) &&

            (res matches Ok(thm) ==> thm.wf(program@))
    {
        if let Some(thm) = self.thms.remove(&event_id) {
            Ok(thm)
        } else {
            Err(TraceError(event_id, "theorem does not exist".to_string()))
        }
    }

    /// Process an event and construct a Theorem with the same statement claimed in the event
    /// Retuen the Theorem object if successful
    pub fn process_event(&mut self, program: &Program, event: &Event, debug: bool) -> (res: Result<&Theorem, TraceError>)
        requires
            old(self).wf(program@) &&
            !old(self).thms@.contains_key(event.id)

            // For simplicity, we assume that the event id coincides with the index of the event
            // event.id == old(self).thms.len()

        ensures
            res matches Ok(thm) ==> (
                self.wf(program@) &&
                thm.wf(program@) &&
                
                self.thms@.contains_key(event.id) &&
                self.thms@[event.id].stmt@ == event.term@ &&
                event.term@ == thm.stmt@
            
                // self.thms has exact one more element
                // self.thms.len() == old(self).thms.len() + 1 &&
                // (forall |i| 0 <= i < old(self).thms.len() ==> old(self).thms[i] == self.thms[i])
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
                    eprint("[debug] applying rule: "); eprintln(rule);
                }

                // Figure out the substitution for the rule application
                let mut subst = Subst::new();
                let mut subproofs: Vec<&Theorem> = vec![];

                // Match rule head against goal first
                if let Err(err) = TermX::match_terms(&mut subst, &rule.head, &event.term) {
                    return Err(TraceError(event.id, err));
                }
            
                // Match each rule body against existing subproof
                for i in 0..subproof_ids.len()
                    invariant
                        subproof_ids.len() == rule.body.len() &&

                        // Invariants to show that subproofs are valid
                        subproofs.len() == i &&
                        self.wf(program@) &&
                        (forall |j| 0 <= j < i ==> (#[trigger] subproofs[j]).wf(program@))
                {
                    subproofs.push(self.get_theorem(program, subproof_ids[i])?);
                    
                    if debug {
                        eprint("[debug]   with subproof: "); eprintln(&subproofs[i].stmt);
                    }

                    if let Err(err) = TermX::match_terms(&mut subst, &rule.body[i], &subproofs[i].stmt) {
                        return Err(TraceError(event.id, err));
                    }
                }

                if debug {
                    eprint("[debug] matching substitution: "); eprintln(&subst);
                }

                // Apply and proof-check the final result 
                if let Some(thm) = Theorem::apply_rule(program, *rule_id, &subst, subproofs) {
                    // TODO: this should be guaranteed if the matching algorithm is correct
                    // prove more about matching to conclude this without the dynamic check.
                    if (&thm.stmt).eq(&event.term) {
                        // Remove the used subproofs to save memory
                        for i in 0..subproof_ids.len()
                            invariant self.wf(program@)
                        {
                            if subproof_ids[i] != event.id {
                                self.remove_theorem(program, subproof_ids[i])?;
                            }
                        }

                        Ok(self.add_theorem(program, event.id, thm))
                    } else {
                        Err(TraceError(event.id, "incorrect matching algorithm".to_string()))
                    }
                } else {
                    Err(TraceError(event.id, "failed to verify proof".to_string()))
                }
            }

            Tactic::AndIntro(left_id, right_id) => {
                let thm = Theorem::and_intro(
                    program,
                    self.get_theorem(program, *left_id)?,
                    self.get_theorem(program, *right_id)?,
                );

                // Check if the statement is consistent with the statement in the trace event
                if (&thm.stmt).eq(&event.term) {
                    self.remove_theorem(program, *left_id)?;
                    self.remove_theorem(program, *right_id)?;
                    Ok(self.add_theorem(program, event.id, thm))
                } else {
                    Err(TraceError(event.id, "incorrect matching algorithm".to_string()))
                }
            }

            Tactic::OrIntroLeft(subproof_id) => {
                match rc_as_ref(&event.term) {
                    TermX::App(f, args) if f.eq(&FnName::user(FN_NAME_OR, 2)) && args.len() == 2 => {
                        let thm = Theorem::or_intro_left(program, self.get_theorem(program, *subproof_id)?, &args[1]);

                        if (&thm.stmt).eq(&event.term) {
                            self.remove_theorem(program, *subproof_id)?;
                            Ok(self.add_theorem(program, event.id, thm))
                        } else {
                            Err(TraceError(event.id, "incorrect matching algorithm".to_string()))
                        }
                    }

                    _ => Err(TraceError(event.id, "incorrect goal".to_string())),
                }
            }

            Tactic::OrIntroRight(subproof_id) => {
                match rc_as_ref(&event.term) {
                    TermX::App(f, args) if f.eq(&FnName::user(FN_NAME_OR, 2)) && args.len() == 2 => {
                        let thm = Theorem::or_intro_right(program, &args[0], self.get_theorem(program, *subproof_id)?);

                        if (&thm.stmt).eq(&event.term) {
                            self.remove_theorem(program, *subproof_id)?;
                            Ok(self.add_theorem(program, event.id, thm))
                        } else {
                            Err(TraceError(event.id, "incorrect matching algorithm".to_string()))
                        }
                    }

                    _ => Err(TraceError(event.id, "incorrect goal".to_string())),
                }
            }

            Tactic::ForallMember(subproof_ids) => {
                let mut subproofs: Vec<&Theorem> = vec![];

                // Collect all subproofs via the ids
                for i in 0..subproof_ids.len()
                    invariant
                        subproofs.len() == i &&
                        self.wf(program@) &&
                        (forall |j| 0 <= j < i ==> (#[trigger] subproofs[j]).wf(program@))
                {
                    subproofs.push(self.get_theorem(program, subproof_ids[i])?);
                }

                if debug {
                    eprint("[debug] apply forall-member: "); eprintln(&event.term);
                }

                if let Some(thm) = Theorem::forall_member(program, &event.term, subproofs) {
                    Ok(self.add_theorem(program, event.id, thm))
                } else {
                    Err(TraceError(event.id, "failed to verify proof".to_string()))
                }
            }

            Tactic::ForallBase(subproof_ids) => {
                let mut subproofs: Vec<&Theorem> = vec![];

                // Collect all subproofs via the ids
                for i in 0..subproof_ids.len()
                    invariant
                        subproofs.len() == i &&
                        self.wf(program@) &&
                        (forall |j| 0 <= j < i ==> (#[trigger] subproofs[j]).wf(program@))
                {
                    subproofs.push(self.get_theorem(program, subproof_ids[i])?);
                }

                if debug {
                    eprint("[debug] apply forall-base: "); eprintln(&event.term);
                }

                if let Some(thm) = Theorem::forall_base(program, &event.term, subproofs) {
                    Ok(self.add_theorem(program, event.id, thm))
                } else {
                    Err(TraceError(event.id, "failed to verify proof".to_string()))
                }
            }

            Tactic::BuiltIn => {
                if let TermX::App(FnName::User(name, arity), args) = rc_as_ref(&event.term) {
                    if *arity != args.len() {
                        return Err(TraceError(event.id, "incorrect unmatched arity".to_string()));
                    }

                    if let Some(thm) = Theorem::try_built_in(program, &event.term) {
                        if (&thm.stmt).eq(&event.term) {
                            return Ok(self.add_theorem(program, event.id, thm));
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

}
