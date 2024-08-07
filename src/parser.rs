use std::rc::Rc;

use peg;

use crate::checker::*;

peg::parser!(grammar prolog() for str {
    rule _ = [' ' | '\n' | '\t' | '\r']*

    // Comma separated list
    rule comma_sep<T>(x: rule<T>) -> Vec<T> = v:(x() ** (_ "," _)) (_ "," _)? { v }

    rule ident() -> &'input str
        = name:$(['a'..='z' | 'A'..='Z']['a'..='z' | 'A'..='Z' | '0'..='9']*) { name }

    rule var() -> &'input str
        = name:$(['_' | 'A'..='Z']['a'..='z' | 'A'..='Z' | '0'..='9']*) { name }

    pub rule term() -> Term
        = var:var() { TermX::var_str(var) }
        / name:ident() _ "(" _ args:comma_sep(<term()>) _ ")" { Rc::new(TermX::App(FnName::user(name, args.len()), args)) }
        / name:ident() { Rc::new(TermX::App(FnName::user(name, 0), vec![])) }

    pub rule clause() -> Rule
        = head:term() _ ":-" _ body:comma_sep(<term()>) _ "." { RuleX::new(head, body) }
        / head:term() _ "." { RuleX::new(head, vec![]) }
});

pub fn test() {
    println!("parsed: {:?}", prolog::term("foo(X, a, b)").unwrap());
    println!("parsed: {:?}", prolog::clause("foo(X, a, b).").unwrap());
    println!("parsed: {:?}", prolog::clause("connected(X, Z) :- edge(X, Y), connected(Y, Z).").unwrap());
    println!("parsed: {:?}", prolog::clause("edge(a, b).").unwrap());
    // assert_eq!(arithmetic::expression("1+1"), Ok(2));
}
