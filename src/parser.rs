use std::rc::Rc;
use std::cell::Cell;
use std::collections::HashMap;

use peg;

use crate::checker::*;
use crate::trace::*;

// Grammar of Prolog
peg::parser!(grammar prolog(line: &Cell<usize>) for str {
    rule _ = s:$quiet!{[' ' | '\t' | '\r' | '\n']*}
        // Count number of new lines
        { line.set(line.get() + s.chars().filter(|c| *c == '\n').count()); }

    /// Comma separated list
    rule comma_sep<T>(x: rule<T>) -> Vec<T> = v:(x() ** (_ "," _)) (_ "," _)? { v }

    /// Returns the slice and the line number
    rule ident() -> (&'input str, usize)
        = name:$(['a'..='z' | 'A'..='Z']['a'..='z' | 'A'..='Z' | '0'..='9']*) { (name, line.get()) }

    rule var() -> (&'input str, usize)
        = name:$(['_' | 'A'..='Z']['a'..='z' | 'A'..='Z' | '0'..='9']*) { (name, line.get()) }

    rule nat() -> usize
        = n:$(['0'..='9']+) { n.parse().unwrap() }

    pub rule term() -> (Term, usize)
        = var:var() { (TermX::var_str(var.0), var.1) }
        / name:ident() _ "(" _ args:comma_sep(<term()>) _ ")" {
            (Rc::new(TermX::App(
                FnName::user(name.0, args.len()),
                args.iter().map(|(arg, _)| arg.clone()).collect(),
            )), name.1)
        }
        / name:ident() { (Rc::new(TermX::App(FnName::user(name.0, 0), vec![])), name.1) }

    pub rule clause() -> (Rule, usize)
        = head:term() _ ":-" _ body:comma_sep(<term()>) _ "."
            { (RuleX::new(head.0, body.iter().map(|(arg, _)| arg.clone()).collect()), head.1) }
        / head:term() _ "."
            { (RuleX::new(head.0, vec![]), head.1) }


    /// Returns a program and a map from line number to rule id
    pub rule program() -> (Program, HashMap<usize, RuleId>)
        = _ rules:(clause() ** _) _ {
            (ProgramX::new(rules.iter().map(|(rule, _)| rule.clone()).collect()),
            rules.iter().enumerate().map(|(i, (_, line))| (*line, i)).collect())
        }

    /// Parser of a trace event
    pub rule event(line_map: &HashMap<usize, RuleId>) -> Event
        = _ id:nat() _ "." _ term:term() _ "by" _ tactic:tactic(line_map) _
            { Event { id, term: term.0, tactic: tactic } }

    rule nested_nat_list() -> Vec<usize>
        = v:nat() { vec![v] }
        / "[" _ l:(nested_nat_list() ** (_ "," _)) _ "]" { l.into_iter().flatten().collect() }

    /// Read a line number, and convert it to a rule id
    /// using the line_map; fails if no entry found in line_map
    rule rule_id(line_map: &HashMap<usize, RuleId>) -> RuleId
        = rule_line:nat() {?
            line_map.get(&rule_line).cloned()
                .ok_or("failed to find rule by the line number")
        }

    rule tactic(line_map: &HashMap<usize, RuleId>) -> Tactic
        = "apply" _ "(" _ "fact" _ "," _ id:rule_id(&line_map) _ ")"
            { Tactic::Apply { rule_id: id, subproof_ids: vec![] } }
        / "apply" _ "(" _ subgoals:nested_nat_list() _ "," _ id:rule_id(&line_map) _ ")"
            { Tactic::Apply { rule_id: id, subproof_ids: subgoals } }
        / "built-in" { Tactic::BuiltIn }
});

/// First argument is the path
#[derive(Debug)]
pub struct ParserError(pub Option<String>, pub peg::error::ParseError<peg::str::LineCol>);

/// Parse a Prolog program source
/// Returns a program and a map from line numbers to rule ids
pub fn parse_program(source: impl AsRef<str>, path: impl AsRef<str>) -> Result<(Program, HashMap<usize, RuleId>), ParserError> {
    let line = Cell::new(1);
    prolog::program(source.as_ref(), &line).map_err(|e| ParserError(Some(path.as_ref().to_string()), e))
}

/// Parse a Prolog term
pub fn parse_term(source: impl AsRef<str>) -> Result<Term, ParserError> {
    let line = Cell::new(1);
    let (term, _) = prolog::term(source.as_ref(), &line)
        .map_err(|e| ParserError(None, e))?;
    Ok(term)
}

/// Parse a trace event
pub fn parse_trace_event(source: impl AsRef<str>, line_map: &HashMap<usize, RuleId>) -> Result<Event, ParserError> {
    let line = Cell::new(1);
    prolog::event(source.as_ref(), &line, &line_map).map_err(|e| ParserError(None, e))
}

pub fn test() {
    let (program, line_map) = parse_program(r#"
node(n0).
node(n1).
node(n2).
node(n3).
edge(n1, n3).
edge(n1, n2).
edge(n0, n1).
source(n0).
destination(n3).
connected(A, B) :- edge(A, B).
connected(A, B) :- edge(A, M), connected(M, B).
query(S, D) :- source(S), destination(D), connected(S, D).
go :- query(n0, n3).
"#, "test.pl").unwrap();

    println!("program: {:?}", program);
    println!("line_map: {:?}", line_map);
}
