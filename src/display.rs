use std::fmt;

use crate::proof::*;
use crate::checker::*;
use crate::parser::escape_string;

impl fmt::Display for FnName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            FnName::User(name, _) => {
                if let Some(first) = name.chars().next() {
                    if first.is_ascii_lowercase() &&
                        name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_' || c == ':') {
                        // Only print the name unescaped if it starts with a-z and
                        // only contains a-z, A-Z, 0-9, _, and :
                        return write!(f, "{}", name);
                    }
                }
                
                write!(f, "'{}'", escape_string(name, '\''))
            },

            // According to https://www.swi-prolog.org/pldoc/man?section=ext-lists
            // [] /= '[]', but functor([1, 2], '[|]', _) is true.
            FnName::Nil => write!(f, "[]"),
            FnName::Cons => write!(f, "'[|]'"),

            FnName::Directive => write!(f, ""),
        }
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Literal::Int(i) => write!(f, "{}", i),
            Literal::String(s) => write!(f, "\"{}\"", escape_string(s, '"')),
        }
    }
}

impl fmt::Display for TermX {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TermX::Var(v) => {
                if v.starts_with('%') {
                    write!(f, "_")
                } else {
                    write!(f, "{}", v)
                }
            },
            TermX::Literal(lit) => write!(f, "{}", lit),
            TermX::App(FnName::Nil, args) if args.len() == 0 => {
                write!(f, "[]")
            }
            TermX::App(FnName::Cons, args) if args.len() == 2 => {
                write!(f, "[{}|{}]", args[0], args[1])
            }
            TermX::App(name, args) if name.eq(&FnName::user(FN_NAME_OR, 2)) && args.len() == 2 => {
                write!(f, "({}; {})", args[0], args[1])
            }
            TermX::App(name, args) if name.eq(&FnName::user(FN_NAME_AND, 2)) && args.len() == 2 => {
                write!(f, "({}, {})", args[0], args[1])
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

        if let TermX::App(FnName::Directive, ..) = self.head.as_ref() {
            write!(f, ":- ")?;
        } else if self.body.len() != 0 {
            write!(f, " :- ")?;
        }

        if self.body.len() != 0 {
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
