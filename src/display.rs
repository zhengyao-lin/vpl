use std::fmt;

use crate::checker::*;

impl fmt::Display for FnName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            FnName::User(name, _) => write!(f, "{}", name),
            FnName::Eq => write!(f, "="),
            FnName::Not => write!(f, "\\+"),
            FnName::Forall => write!(f, "forall"),

            // TODO: better way to print these?
            FnName::Nil => write!(f, "'[]'"),
            FnName::Cons => write!(f, "'[|]'"),
        }
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Literal::Int(i) => write!(f, "{}", i),
            // TODO: escapte s
            Literal::String(s) => write!(f, "\"{}\"", s),
        }
    }
}

impl fmt::Display for TermX {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TermX::Var(v) => write!(f, "{}", v),
            TermX::Literal(lit) => write!(f, "{}", lit),
            TermX::App(FnName::Nil, args) if args.len() == 0 => {
                write!(f, "[]")
            }
            TermX::App(FnName::Cons, args) if args.len() == 2 => {
                write!(f, "[{}|{}]", args[0], args[1])
            }
            TermX::App(name, args) => {
                write!(f, "{}", name)?;
                if args.len() != 0 {
                    write!(f, "(")?;
                    for (i, arg) in args.iter().enumerate() {
                        if i == 0 {
                            write!(f, "{}", arg)?;
                        } else {
                            write!(f, ", {}", arg)?;
                        }
                    }
                    write!(f, ")")
                } else {
                    Ok(())
                }
            }
        }
    }
}

impl fmt::Display for RuleX {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.head)?;

        if self.body.len() != 0 {
            write!(f, " :- ")?;
            for (i, term) in self.body.iter().enumerate() {
                if i == 0 {
                    write!(f, "{}", term)?;
                } else {
                    write!(f, ", {}", term)?;
                }
            }
        }
        
        write!(f, ".")
    }
}

impl fmt::Display for Subst {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{{")?;
        for (i, (k, v)) in self.0.m.iter().enumerate() {
            if i == 0 {
                write!(f, "{} -> {}", k, v)?;
            } else {
                write!(f, ", {} -> {}", k, v)?;
            }
        }
        write!(f, "}}")
    }
}

impl fmt::Display for crate::trace::TraceError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "failed to verify event {}: {}", self.0, self.1)
    }
}

impl fmt::Display for crate::parser::ParserError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.0 {
            Some(path) => write!(f, "{}", path)?,
            None => write!(f, "<unknown>")?,
        }
        write!(f, ":{}:{}: expecting {}", self.1.location.line, self.1.location.column, self.1.expected)
    }
}
