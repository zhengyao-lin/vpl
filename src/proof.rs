use vstd::prelude::*;

// Define proofs of queries in Prolog

verus! {

pub const FN_NAME_EQ: &'static str = "=";
pub const FN_NAME_EQUIV: &'static str = "==";
pub const FN_NAME_NOT: &'static str = "\\+";

pub type SpecVar = Seq<char>;
pub type SpecUserFnName = Seq<char>;
pub type SpecRuleId = int;
pub type SpecArity = int;
pub type SpecIntLiteral = int;
pub type SpecStringLiteral = Seq<char>;

pub enum SpecFnName {
    // User-defined symbol: (name, arity)
    User(SpecUserFnName, SpecArity),

    // List nil/0 and cons/2
    Nil,
    Cons,
}

pub enum SpecLiteral {
    Int(SpecIntLiteral),
    String(SpecStringLiteral),
}

pub enum SpecTerm {
    Var(SpecVar),
    Literal(SpecLiteral),
    App(SpecFnName, Seq<SpecTerm>),
}

pub struct SpecRule {
    pub head: SpecTerm,
    pub body: Seq<SpecTerm>,
}

pub struct SpecProgram {
    pub rules: Seq<SpecRule>,
}

pub struct SpecSubst(pub Map<SpecVar, SpecTerm>);

/// A proof includes a statement and its proof tree
/// Free variables in the statement are implicitly existentially quantified
pub struct SpecTheorem {
    pub stmt: SpecTerm,
    pub proof: SpecProof,
}

pub enum SpecProof {
    // Apply an instance of an existing rule
    ApplyRule { rule_id: SpecRuleId, subst: SpecSubst, subproofs: Seq<SpecTheorem> },
    
    // Proves t = t
    Refl,

    // // For all base facts, certain query is true
    // // i.e. proves forall(p(x_1, ..., x_n), q(...))
    // // where p is a base predicate
    // ForallBase { subproofs: Seq<SpecTheorem> },

    // Proves ground and base version of \+P(...)
    NotBase,

    // TODO: Need an entire class of proof rules for proving
    // negation of queries (e.g. for conjunction, disjunction, etc.)
}

impl SpecTerm {
    /// Get free variables in a term
    pub closed spec fn free_vars(self) -> Set<SpecVar>
        decreases self
    {
        match self {
            SpecTerm::Var(v) => Set::new(|u| u == v),
            SpecTerm::Literal(..) => Set::empty(),
            SpecTerm::App(_, args) =>
                Set::new(|v| exists |i|
                    #![trigger args[i].free_vars()]
                    0 <= i < args.len() && args[i].free_vars().contains(v)),
        }
    }

    /// Substitute a term
    /// TODO: Using an axiom here due to Verus issue #1222
    pub closed spec fn subst(self, subst: SpecSubst) -> SpecTerm;
    #[verifier::external_body]
    pub broadcast proof fn axiom_subst(self, subst: SpecSubst)
        ensures #[trigger] self.subst(subst) == match self {
            SpecTerm::Var(v) => if subst.contains_var(v) { subst.get(v) } else { self },
            SpecTerm::Literal(..) => self,
            SpecTerm::App(f, args) => SpecTerm::App(f, args.map_values(|arg: SpecTerm| arg.subst(subst))),
        }
    {}

    /// Check if a term is headed in the given name
    pub open spec fn is_app_of(self, name: SpecFnName) -> bool {
        self matches SpecTerm::App(f, ..) && f == name
    }

    pub open spec fn args(self) -> Seq<SpecTerm> {
        self->App_1
    }
}

impl SpecSubst {
    pub open spec fn get(self, v: SpecVar) -> SpecTerm {
        self.0[v]
    }

    pub open spec fn dom(self) -> Set<SpecVar> {
        self.0.dom()
    }

    pub open spec fn contains_var(self, v: SpecVar) -> bool {
        self.0.contains_key(v)
    }
}

impl SpecRule {
    /// Check if the rule is stating a base fact, i.e.,
    /// the rule has no body and no free variables
    pub open spec fn is_base_fact(self) -> bool {
        self.body.len() == 0 &&
        self.head.free_vars().is_empty()
    }
}

impl SpecProgram {
    // Check if all rules headed by `name` is ground and has no body
    pub open spec fn is_base_pred(self, name: SpecFnName) -> bool {
        forall |i|
            0 <= i < self.rules.len() &&
            (#[trigger] self.rules[i]).head.is_app_of(name)
            ==>
            self.rules[i].is_base_fact()
    }
}

impl SpecTheorem {
    /// Defines whether a proof is well-formed
    pub open spec fn wf(self, program: SpecProgram) -> bool
        decreases self
    {
        match self.proof {
            SpecProof::ApplyRule { rule_id, subst, subproofs } => {
                &&& 0 <= rule_id < program.rules.len()

                // Subproofs correspond to each term in the body of the rule
                &&& subproofs.len() == program.rules[rule_id].body.len()
                &&& forall |i| 0 <= i < subproofs.len() ==>
                    #[trigger] program.rules[rule_id].body[i].subst(subst) == (#[trigger] subproofs[i]).stmt

                // All subproofs are well-formed
                &&& forall |i| 0 <= i < subproofs.len() ==> (#[trigger] subproofs[i]).wf(program)

                // NOTE: we do not require subst to cover all free variables in the rule
                // because we need to allow proofs for terms such as forall(p(x), q(x)),
                // in which x can remain as a variable.
            }

            SpecProof::Refl => {
                &&& self.stmt matches SpecTerm::App(f, args)
                &&& f == SpecFnName::User(FN_NAME_EQ.view(), 2) || f == SpecFnName::User(FN_NAME_EQUIV.view(), 2)
                &&& args.len() == 2
                &&& args[0] == args[1]
            }

            // ForallBase { subproofs: Seq<SpecTheorem> } => {
            //     // self.stmt is of the form forall(p(...), q(...))
            //     &&& self.stmt matches SpecTerm::App(SpecFnName::Forall, forall_args)
            //     &&& forall_args.len() == 2

            //     // p is a base predicate
            //     &&& forall_args[0] matches SpecTerm::App(name, args)
            //     &&& program.is_base_pred(name)

            //     // TODO: for each base fact of p that can unify with p(...)
            //     // we need to have a subproof of q(...)
            // }

            // Proves negation for a base predicate
            SpecProof::NotBase => {
                // self.stmt is of the form \+P(...)
                &&& self.stmt matches SpecTerm::App(f, not_args)
                &&& f == SpecFnName::User(FN_NAME_NOT.view(), 1)
                &&& not_args.len() == 1

                // P is a base predicate and P(...) is ground
                &&& not_args[0] matches SpecTerm::App(name, args)
                &&& program.is_base_pred(name)
                &&& not_args[0].free_vars().is_empty()

                // P(...) is NOT a fact in the program
                &&& forall |i|
                    0 <= i < program.rules.len() &&
                    (#[trigger] program.rules[i]).head.is_app_of(name)
                    ==>
                    program.rules[i].head.args().len() == args.len() &&
                    program.rules[i].head.args() != args
            }
        }
    }
}

}

