use std::rc::Rc;
use std::cell::Cell;
use std::collections::HashMap;

use peg;

use crate::checker::*;
use crate::trace::*;

// Grammar of Prolog
peg::parser!(grammar prolog(line: &Cell<usize>) for str {
    rule ignore()
        // whitespaces
        = quiet!{[' ' | '\t' | '\r']}
        / quiet!{"\n"} { line.set(line.get() + 1); }
        // Inline comments
        / "%" [^'\n']* // { line.set(line.get() + 1); }

    rule _ = ignore()*

    /// Comma separated list without extra trailing comma
    rule comma_sep<T>(x: rule<T>) -> Vec<T> = v:(x() ** (_ "," _)) { v }

    /// Same as comma_sep, but requires at least one element
    rule comma_sep_plus<T>(x: rule<T>) -> Vec<T> = v:(x() ++ (_ "," _)) { v }

    /// Returns the slice and the line number
    rule ident() -> (&'input str, usize)
        = name:quiet!{$(['a'..='z' | 'A'..='Z']['a'..='z' | 'A'..='Z' | '0'..='9']*)} { (name, line.get()) }
        / "'" name:$([^'\'']*) "'" { (name, line.get()) }
        / expected!("identifier")

    rule var() -> (&'input str, usize)
        = name:quiet!{$(['_' | 'A'..='Z']['a'..='z' | 'A'..='Z' | '0'..='9']*)} { (name, line.get()) }
        / expected!("variable")

    rule nat() -> usize
        = n:quiet!{$(['0'..='9']+)} {? n.parse().map_err(|_| "failed to parse nat") }
        / expected!("nat")

    rule int() -> i64
        = n:quiet!{$("-"?['0'..='9']+)} {? n.parse().map_err(|_| "failed to parse int") }
        / expected!("int")

    /// TODO: handle escape strings and newlines
    /// also see https://www.swi-prolog.org/pldoc/man?section=charescapes
    rule string() -> &'input str
        = "\"" s:$([^'"']*) "\"" { s }
        / expected!("string")

    /// Used for getting the line number
    rule list_left_bracket() -> usize
        = "[" { line.get() }

    /// Prolog lists, e.g., [], [a,b|[]], [a,b,c]
    rule list() -> (Term, usize)
        = brak_line:list_left_bracket() _ "]" { (Rc::new(TermX::App(FnName::Nil, vec![])), brak_line) }
        / brak_line:list_left_bracket() _ elems:comma_sep_plus(<term()>) _ "]"
            {
                let mut list = Rc::new(TermX::App(FnName::Nil, vec![]));
                for elem in elems.into_iter().rev() {
                    list = Rc::new(TermX::App(FnName::Cons, vec![elem.0, list]));
                }
                (list, brak_line)
            }
        / brak_line:list_left_bracket() _ heads:comma_sep_plus(<term()>) _ "|" _ tail:term() _ "]"
            {
                let mut list = tail.0;
                for head in heads.into_iter().rev() {
                    list = Rc::new(TermX::App(FnName::Cons, vec![head.0, list]));
                }
                (list, brak_line)
            }

    /// Prolog terms
    pub rule term() -> (Term, usize)
        = var:var() { (TermX::var_str(var.0), var.1) }

        // Literals
        / i:int() { (Rc::new(TermX::Literal(Literal::Int(i))), line.get()) }
        // TODO: string may range multiple lines, fix the line number
        / s:string() { (Rc::new(TermX::Literal(Literal::String(s.into()))), line.get()) }

        // Application (including atoms and lists)
        / name:ident() _ "(" _ args:comma_sep(<term()>) _ ")" {
            (Rc::new(TermX::App(
                FnName::user(name.0, args.len()),
                args.iter().map(|(arg, _)| arg.clone()).collect(),
            )), name.1)
        }
        / name:ident() { (Rc::new(TermX::App(FnName::user(name.0, 0), vec![])), name.1) }
        / list:list() { list }

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
