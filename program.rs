use std::rc::Rc;
use vstd::prelude::*;

use crate::containers::StringHashMap;
use crate::semantics::*;

verus! {

pub type Var = String;
pub type Const = String;
pub type Int = i64;
pub type FnName = String;

pub type Term = Rc<TermX>;
pub enum TermX {
    Var(Var),
    App(FnName, Vec<Term>),
}

pub type Rule = Rc<RuleX>;
pub struct RuleX {
    pub head: Term,
    pub body: Vec<Term>,
}

pub type Program = Rc<ProgramX>;
pub struct ProgramX {
    pub rules: Vec<Rule>,
}

pub struct Subst(pub StringHashMap<Term>);

pub struct Goal {
    pub subst: Subst,
    pub subgoals: Vec<Term>,
}

impl DeepView for TermX {
    type V = SpecTerm;
    /// TODO: Verus issue #1222
    closed spec fn deep_view(&self) -> Self::V;
}

impl TermX {
    #[verifier::external_body]
    pub broadcast proof fn axiom_deep_view(&self)
        ensures #[trigger] self.deep_view() == match self {
            TermX::Var(v) => SpecTerm::Var(v.view()),
            TermX::App(name, args) => SpecTerm::App(name.view(), Seq::new(args.len() as nat, |i| args[i].deep_view())),
        }
    {}
}

impl DeepView for RuleX {
    type V = SpecRule;

    open spec fn deep_view(&self) -> Self::V {
        SpecRule {
            head: self.head.deep_view(),
            body: Seq::new(self.body.len() as nat, |i| self.body[i].deep_view()),
        }
    }
}

impl DeepView for ProgramX {
    type V = SpecProgram;

    open spec fn deep_view(&self) -> Self::V {
        SpecProgram {
            rules: Seq::new(self.rules.len() as nat, |i| self.rules[i].deep_view()),
        }
    }
}

impl DeepView for Subst {
    type V = SpecSubst;

    open spec fn deep_view(&self) -> Self::V {
        SpecSubst(Map::total(|v| if self.0.view().dom().contains(v) {
            self.0.view()[v].deep_view()
        } else {
            // Undefined entries default to identity
            SpecTerm::Var(v)
        }))
    }
}

impl DeepView for Goal {
    type V = SpecGoal;

    open spec fn deep_view(&self) -> Self::V {
        SpecGoal {
            subst: self.subst.deep_view(),
            subgoals: Seq::new(self.subgoals.len() as nat, |i| self.subgoals[i].deep_view()),
        }
    }
}

impl TermX {
    pub fn constant(name: &str) -> Term {
        Rc::new(TermX::App(name.to_string(), vec![]))
    }

    pub fn app(name: &str, args: Vec<Term>) -> Term {
        Rc::new(TermX::App(name.to_string(), args))
    }

    pub fn var(name: &str) -> Term {
        Rc::new(TermX::Var(name.to_string()))
    }

    pub fn subst(&self, subst: &Subst) -> Term {
        // TODO
        TermX::constant("not implemented")
    }
}

impl Subst {
    pub fn new() -> Subst {
        Subst(StringHashMap::new())
    }

    /**
     * Apply self to each value of other and return a new substitution
     */
    pub fn compose(&self, other: &Subst) -> Subst {
        // TODO
        Subst::new()
    }
}

// impl Goal {
//     pub open spec fn view(self) -> SpecGoal {
//         todo!()
//     }
// }

/**
 * edge(n1, n2).
 * edge(n2, n3).
 * 
 * connected(A, B) :- edge(A, B).
 * connected(A, C) :- edge(A, B), connected(B, C).
 * 
 * :- connected(n1, n3).
 */

/**
 * Assume the existence of a unification algorithm
 */
fn unify(t1: Term, t2: Term) -> Option<Subst> { None }

fn edge(cur_subst: &Subst, t1: &Term, t2: &Term) -> Option<Subst> {
    // Rule edge(n1, n2)
    if let Some(subst) = unify(
        TermX::app("edge", vec![ TermX::constant("n1"), TermX::constant("n2") ]),
        TermX::app("edge", vec![ t1.clone(), t2.clone() ]),
    ) {
        return Some(subst.compose(cur_subst));
    }

    // Rule edge(n2, n3)
    if let Some(subst) = unify(
        TermX::app("edge", vec![ TermX::constant("n2"), TermX::constant("n3") ]),
        TermX::app("edge", vec![ t1.clone(), t2.clone() ]),
    ) {
        return Some(subst.compose(cur_subst));
    }

    return None;
}

fn connected(cur_subst: &Subst, t1: &Term, t2: &Term) -> Option<Subst> {
    // Rule connected(A, B) :- edge(A, B)
    if let Some(subst) = edge(cur_subst, t1, t2) {
        return Some(subst);
    }

    // Rule connected(A, C) :- edge(A, B), connected(B, C)
    if let Some(subst1) = edge(cur_subst, t1, &TermX::var("B")) {
        if let Some(subst2) = connected(&subst1, &(&TermX::var("B")).subst(&subst1), &t2.subst(&subst1)) {
            return Some(subst2);
        }
    }

    return None;
}

fn solve() -> bool {
    connected(&Subst::new(), &TermX::constant("n1"), &TermX::constant("n3")).is_some()
}

// // #[verifier::external_fn_specification]
// // #[verifier::when_used_as_spec(as_ref)]
// #[verifier::external_body]
// pub fn rc_as_ref<T: DeepView>(rc: &Rc<T>) -> (res: &T)
//     ensures rc.deep_view() == res.deep_view()
// {
//     rc.as_ref()
// }

// pub fn edge(t1: &Term, t2: &Term) -> (r: Vec<Subst>)
//     ensures r.len() != 0 ==>
//         (t1.deep_view() == SpecTerm::App("n1".view(), seq![]) ||
//          t1.deep_view() == SpecTerm::App("n2".view(), seq![]))
// {
//     match (rc_as_ref(t1), rc_as_ref(t2)) {
//         (TermX::App(c1, args1), TermX::App(c2, args2)) if args1.len() == 0 && args2.len() == 0 => {
//             proof {
//                 assert(t1.deep_view() matches SpecTerm::App(_, args) && args == seq![]);
//             }
//             if c1.eq(&"n1".to_string()) && c2.eq(&"n2".to_string()) {
//                 proof {
//                     TermX::axiom_deep_view();
//                 }
//                 vec![Subst(StringHashMap::new())]
//             } else if c1.eq(&"n2".to_string()) && c2.eq(&"n3".to_string()) {
//                 proof {
//                     TermX::axiom_deep_view();
//                 }
//                 vec![Subst(StringHashMap::new())]
//             } else {
//                 vec![]
//             }
//         }
//         _ => vec![],
//     }
// }

fn test() {
    let term1 = Rc::new(TermX::App("n1".to_string(), vec![]));
    let term2 = Rc::new(TermX::App("edge".to_string(), vec![term1.clone(), term1.clone()]));
    
    proof {
        broadcast use TermX::axiom_deep_view;
        assert(term1.deep_view()->App_1 =~= seq![]);
        assert(term1.deep_view() == SpecTerm::App("n1".view(), seq![]));
        // assert(term2.deep_view() matches SpecTerm::App(_, s) ==> s == seq![term1.deep_view(), term1.deep_view()]);
        // assert(term2.deep_view() =~= SpecTerm::App("edge".view(), seq![ SpecTerm::App("n1".view(), seq![]), SpecTerm::App("n1".view(), seq![]) ]));
    }
}

}
