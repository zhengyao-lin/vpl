use std::rc::Rc;
use std::cell::Cell;
use std::collections::HashMap;

use peg;

use crate::proof::*;
use crate::checker::*;
use crate::trace::*;

/// e.g. edge(_, _) => edge(%1, %2)
/// when displaying, all variables starting with % is replaced with _
pub const ANON_VAR_PREFIX: &'static str = "%";

struct ParserState {
    line: Cell<usize>,
    anon_var_counter: Cell<usize>,
}

impl ParserState {
    fn new() -> ParserState {
        ParserState {
            line: Cell::new(1),
            anon_var_counter: Cell::new(0),
        }
    }

    fn line(&self) -> usize {
        self.line.get()
    }

    fn inc_line(&self) {
        self.line.set(self.line.get() + 1);
    }

    fn fresh_anon_var(&self) -> String {
        let counter = self.anon_var_counter.get();
        self.anon_var_counter.set(counter + 1);
        format!("{}{}", ANON_VAR_PREFIX, counter)
    }
}

// Grammar of Prolog
peg::parser!(grammar prolog(state: &ParserState) for str {
    rule ignore()
        // whitespaces
        = quiet!{[' ' | '\t' | '\r']}
        / quiet!{"\n"} { state.inc_line(); }
        // Inline comments
        / "%" [^'\n']*

    rule _ = ignore()*

    rule line() -> usize = { state.line() }

    /// Comma separated list without extra trailing comma
    rule comma_sep<T>(x: rule<T>) -> Vec<T> = v:(x() ** (_ "," _)) { v }

    /// Same as comma_sep, but requires at least one element
    rule comma_sep_plus<T>(x: rule<T>) -> Vec<T> = v:(x() ++ (_ "," _)) { v }

    /// Returns the slice and the line number
    rule ident() -> &'input str
        = name:quiet!{$(['a'..='z' | 'A'..='Z']['_' | 'a'..='z' | 'A'..='Z' | '0'..='9']*)} { name }
        / "'" name:$([^'\'']*) "'" { name }
        / expected!("identifier")

    rule var() -> &'input str
        = name:quiet!{$(['A'..='Z']['_' | 'a'..='z' | 'A'..='Z' | '0'..='9']*)} { name }
        / name:quiet!{$(['_']['_' | 'a'..='z' | 'A'..='Z' | '0'..='9']+)} { name }
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

    /// Prolog lists, e.g., [], [a,b|[]], [a,b,c]
    rule list() -> Term
        = "[" _ "]" { Rc::new(TermX::App(FnName::Nil, vec![])) }
        / "[" _ elems:comma_sep_plus(<small_term()>) _ "]"
            {
                let mut list = Rc::new(TermX::App(FnName::Nil, vec![]));
                for elem in elems.into_iter().rev() {
                    list = Rc::new(TermX::App(FnName::Cons, vec![elem, list]));
                }
                list
            }
        / "[" _ heads:comma_sep_plus(<small_term()>) _ "|" _ tail:small_term() _ "]"
            {
                let mut list = tail;
                for head in heads.into_iter().rev() {
                    list = Rc::new(TermX::App(FnName::Cons, vec![head, list]));
                }
                list
            }

    /// Prolog terms
    /// See https://www.swi-prolog.org/pldoc/man?section=operators
    /// for default precedence of operators
    /// 
    /// See https://docs.rs/peg/latest/peg/ for precedence!
    pub rule term() -> Term = precedence! {
        t1:@ _ ";" _ t2:(@) { Rc::new(TermX::App(FnName::user(FN_NAME_OR, 2), vec![t1, t2])) }
        --
        t1:@ _ "," _ t2:(@) { Rc::new(TermX::App(FnName::user(FN_NAME_AND, 2), vec![t1, t2])) }
        --
        t:small_term() { t }
    }

    /// Terms without comma or disjunction
    /// This is to avoid [a, b, c] being parsed as a singleton list of conjunction (a, b, c)
    /// 
    /// TODO: Prolog syntax is weird.
    /// For example, disjunction (;/2) has lower precedence than conjunction (,/2).
    /// However, we have
    /// - Illegal: [a|b,c]
    /// - Legal: [a|(b;c)]
    /// - Legal: [a|(b,c)]
    pub rule small_term() -> Term = precedence! {
        "\\+" _ t:@ { Rc::new(TermX::App(FnName::user(FN_NAME_NOT, 1), vec![t])) }
        --
        t1:@ _ "=" _ t2:(@) { Rc::new(TermX::App(FnName::user(FN_NAME_EQ, 2), vec![t1, t2])) }
        t1:@ _ "\\=" _ t2:(@) { Rc::new(TermX::App(FnName::user(FN_NAME_NOT_EQ, 2), vec![t1, t2])) }
        t1:@ _ "==" _ t2:(@) { Rc::new(TermX::App(FnName::user(FN_NAME_EQUIV, 2), vec![t1, t2])) }
        t1:@ _ "\\==" _ t2:(@) { Rc::new(TermX::App(FnName::user(FN_NAME_NOT_EQUIV, 2), vec![t1, t2])) }
        --
        t1:(@) _ "+" _ t2:@ { Rc::new(TermX::App(FnName::user(FN_NAME_ADD, 2), vec![t1, t2])) }
        t1:(@) _ "/" _ t2:@ { Rc::new(TermX::App(FnName::user(FN_NAME_PRED_IND, 2), vec![t1, t2])) }
        --

        // Same as ( t ) but we need to get the line number
        // of the first parenthesis
        "(" t:term() ")" { t }

        var:var() { TermX::var_str(var) }
        
        // There is a special case of the anonymous variable "_"
        // different occurrences of "_" in a clause is considered different variables
        // so we need to generate fresh names for them
        "_" { TermX::var_str(&state.fresh_anon_var()) }

        // Literals
        i:int() { Rc::new(TermX::Literal(Literal::Int(i))) }
        // TODO: string may range multiple lines, fix the line number
        s:string() { Rc::new(TermX::Literal(Literal::String(s.into()))) }

        // Application (including atoms and lists)
        name:ident() _ "(" _ args:comma_sep(<small_term()>) _ ")" {
            Rc::new(TermX::App(FnName::user(name, args.len()), args))
        }
        name:ident() { Rc::new(TermX::App(FnName::user(name, 0), vec![])) }
        list:list() { list }
    }

    pub rule clause() -> (Rule, usize)
        = line:line() head:term() _ "."
            { (RuleX::new(head, vec![]), line) }

        // Conjunction as a binary operator
        / line:line() head:term() _ ":-" _ body:term() _ "."
            { (RuleX::new(head, vec![body]), line) }

        // Headless clauses are converted into `true :- ... .`
        / line:line() ":-" _ body:term() _ "."
            {
                let head = Rc::new(TermX::App(FnName::user(FN_NAME_TRUE, 0), vec![]));
                (RuleX::new(head, vec![body]), line)
            }

    /// Returns a program and a map from line number to rule id
    pub rule program() -> (Program, HashMap<usize, RuleId>)
        = _ rules:(clause() ** _) _ {
            let mut program_rules = vec![];
            let mut line_map = HashMap::new();

            for (i, (rule, line)) in rules.into_iter().enumerate() {
                program_rules.push(rule);
                line_map.insert(line, i);
            }

            (ProgramX::new(program_rules), line_map)
        }

    /// Parser of a trace event
    pub rule event(line_map: &HashMap<usize, RuleId>) -> Event
        = _ id:nat() _ "." _ term:term() _ "by" _ tactic:tactic(line_map) _
            { Event { id, term: term, tactic: tactic } }

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
        / "and" _ "(" _ left:nat() _ "," _ right:nat() _ ")"
            { Tactic::AndIntro(left, right) }
        / "or-left" _ "(" _ left:nat() _ ")"
            { Tactic::OrIntroLeft(left) }
        / "or-right" _ "(" _ right:nat() _ ")"
            { Tactic::OrIntroRight(right) }
        / "forall-member" _ "(" _ subproofs:nested_nat_list() _ ")"
            { Tactic::ForallMember(subproofs) }
        / "forall-base" _ "(" _ subproofs:nested_nat_list() _ ")"
            { Tactic::ForallBase(subproofs) }
        / "built-in" { Tactic::BuiltIn }
});

/// First argument is the path
#[derive(Debug)]
pub struct ParserError(pub Option<String>, pub peg::error::ParseError<peg::str::LineCol>);

/// Parse a Prolog program source
/// Returns a program and a map from line numbers to rule ids
pub fn parse_program(source: impl AsRef<str>, path: impl AsRef<str>) -> Result<(Program, HashMap<usize, RuleId>), ParserError> {
    let state = ParserState::new();
    prolog::program(source.as_ref(), &state).map_err(|e| ParserError(Some(path.as_ref().to_string()), e))
}

/// Parse a Prolog term
pub fn parse_term(source: impl AsRef<str>) -> Result<Term, ParserError> {
    let state = ParserState::new();
    prolog::term(source.as_ref(), &state)
        .map_err(|e| ParserError(None, e))
}

/// Parse a trace event
pub fn parse_trace_event(source: impl AsRef<str>, line_map: &HashMap<usize, RuleId>) -> Result<Event, ParserError> {
    let state = ParserState::new();
    prolog::event(source.as_ref(), &state, &line_map).map_err(|e| ParserError(None, e))
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
