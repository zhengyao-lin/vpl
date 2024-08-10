use vstd::prelude::*;

// Define proofs of queries in Prolog

verus! {

pub const FN_NAME_TRUE: &'static str = "true";
pub const FN_NAME_AND: &'static str = ",";
pub const FN_NAME_OR: &'static str = ";";
pub const FN_NAME_EQ: &'static str = "="; // equality checks for unification
pub const FN_NAME_NOT_EQ: &'static str = "\\=";
pub const FN_NAME_EQUIV: &'static str = "=="; // equivalence checks for syntactic equality (e.g. X \== Y)
pub const FN_NAME_NOT_EQUIV: &'static str = "\\==";
pub const FN_NAME_NOT: &'static str = "\\+";
pub const FN_NAME_FORALL: &'static str = "forall";
pub const FN_NAME_MEMBER: &'static str = "member";
pub const FN_NAME_LENGTH: &'static str = "length";
pub const FN_NAME_PRED_IND: &'static str = "/"; // e.g. functor/3
pub const FN_NAME_ADD: &'static str = "+";

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

#[verifier::ext_equal]
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
    
    // Show a, b if we have proven a and b separately
    AndIntro(Box<SpecTheorem>, Box<SpecTheorem>),

    // Show a; b if we have proven a or b
    OrIntroLeft(Box<SpecTheorem>),
    OrIntroRight(Box<SpecTheorem>),

    // Proves goals of the form
    //   forall(member(X, L), <Goal>)
    // where X has to be a variable
    // and L has to be a concrete list
    ForallMember(Seq<SpecTheorem>),

    // Proves goals of the form
    //   forall(P(...), Q(...))
    // where P is a base predicate
    ForallBase(Seq<SpecTheorem>),

    /// Built-in function evaluation for integers, strings, and lists
    BuiltIn,
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

    /// Try to convert a term in the form of a Prolog list [t1 | [t2 | ...]]
    /// to a Seq of terms [t1, t2, ...]
    /// If there are non-cons or non-nil terms, return None
    pub open spec fn as_list(self) -> Option<Seq<SpecTerm>>
        decreases self
    {
        match self {
            SpecTerm::App(SpecFnName::Nil, args) => if args.len() == 0 { Some(seq![]) } else { None },
            SpecTerm::App(SpecFnName::Cons, args) =>
                if args.len() == 2 {
                    match args[1].as_list() {
                        Some(tail) => {
                            Some(seq![args[0]] + tail)
                        }
                        None => None,
                    }
                } else {
                    None
                },
            _ => None,
        }
    }

    /// Specifies a sufficient condition for two terms to be non-unifiable
    /// NOTE: this does not completely cover non-unifiability
    pub open spec fn not_unifiable(self, other: SpecTerm) -> bool
        decreases self
    {
        match (self, other) {
            (SpecTerm::Literal(l1), SpecTerm::Literal(l2)) => l1 != l2,

            // Distinct head symbol, or non-unifiable subterms
            (SpecTerm::App(f1, args1), SpecTerm::App(f2, args2)) =>
                f1 != f2 ||
                args1.len() != args2.len() ||
                (exists |i| 0 <= i < args1.len() && (#[trigger] args1[i]).not_unifiable(#[trigger] args2[i])),

            _ => false,
        }
    }

    // /// `self` matches `other` iff there is a substitution `subst`
    // /// such that `self.subst(subst) == other`
    // pub open spec fn matches(self, other: SpecTerm) -> bool {
    //     exists |subst: SpecSubst| #[trigger] self.subst(subst) == other
    // }

    /// Check if self matches other
    /// i.e. variables in other are considered constants
    /// and variables in self are used for unification
    pub closed spec fn matches(self, other: SpecTerm) -> Option<SpecSubst>;
    #[verifier::external_body]
    pub broadcast proof fn axiom_matches(self, other: SpecTerm)
        ensures #[trigger] self.matches(other) == match (self, other) {
            (SpecTerm::Var(v), _) => Some(SpecSubst(map!{ v => other })),

            (SpecTerm::Literal(l1), SpecTerm::Literal(l2)) =>
                if l1 == l2 {
                    Some(SpecSubst::empty())
                } else {
                    None
                },

            (SpecTerm::App(f1, args1), SpecTerm::App(f2, args2)) =>
                if f1 == f2 && args1.len() == args2.len() {
                    SpecTerm::matches_multiple(args1, args2)
                } else {
                    None
                },

            _ => None,
        }
    {}

    /// Match multiple terms and merge substitutions
    pub open spec fn matches_multiple(terms1: Seq<SpecTerm>, terms2: Seq<SpecTerm>) -> Option<SpecSubst>
        decreases terms1.len()
    {
        if terms1.len() != terms2.len() {
            None
        } else if terms1.len() == 0 {
            Some(SpecSubst(map!{}))
        } else {
            match terms1[0].matches(terms2[0]) {
                Some(subst1) => {
                    match SpecTerm::matches_multiple(terms1.drop_first(), terms2.drop_first()) {
                        Some(subst2) => subst1.merge(subst2),
                        None => None,
                    }
                }
                None => None,
            }
        }
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

    pub open spec fn empty() -> SpecSubst {
        SpecSubst(Map::empty())
    }

    pub open spec fn is_empty(self) -> bool {
        self.dom() == Set::<SpecVar>::empty()
    }

    pub open spec fn mergeable(self, other: SpecSubst) -> bool {
        forall |v| #[trigger] self.contains_var(v) && other.contains_var(v) ==>
            self.get(v) == other.get(v)
    }

    /// Two substitutions are mergeable if they agree on the
    /// intersection of their domains
    pub open spec fn merge(self, other: SpecSubst) -> Option<SpecSubst> {
        if self.mergeable(other) {
            Some(SpecSubst(Map::new(
                |v| self.contains_var(v) || other.contains_var(v),
                |v| if self.contains_var(v) {
                    self.get(v)
                } else {
                    other.get(v)
                }
            )))
        } else {
            None
        }
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

/// Similar to iterator's filter_map
pub open spec fn filter_map<T, S>(s: Seq<T>, f: spec_fn(T) -> Option<S>) -> Seq<S>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        match f(s[0]) {
            Some(v) => seq![v] + filter_map(s.drop_first(), f),
            None => filter_map(s.drop_first(), f),
        }
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

                // The final conclusion should coincide with head of the rule after subst
                &&& program.rules[rule_id].head.subst(subst) == self.stmt

                // NOTE: we do not require subst to cover all free variables in the rule
                // because we need to allow proofs for terms such as forall(p(x), q(x)),
                // in which x can remain as a variable.
            }

            SpecProof::AndIntro(left, right) => {
                &&& self.stmt matches SpecTerm::App(f, args)
                &&& f == SpecFnName::User(FN_NAME_AND.view(), 2)
                &&& args.len() == 2
                &&& left.stmt == args[0]
                &&& right.stmt == args[1]
            }

            SpecProof::OrIntroLeft(subproof) => {
                &&& self.stmt matches SpecTerm::App(f, args)
                &&& f == SpecFnName::User(FN_NAME_OR.view(), 2)
                &&& args.len() == 2
                &&& subproof.stmt == args[0]
            }

            SpecProof::OrIntroRight(subproof) => {
                &&& self.stmt matches SpecTerm::App(f, args)
                &&& f == SpecFnName::User(FN_NAME_OR.view(), 2)
                &&& args.len() == 2
                &&& subproof.stmt == args[1]
            }

            SpecProof::ForallMember(subproofs) => {
                // Check that the statement of the form
                //   forall(member(X, L), <Goal>)
                // where X has to be a variable
                // and L has to be a concrete list
                &&& self.stmt matches SpecTerm::App(f, forall_args)
                &&& f == SpecFnName::User(FN_NAME_FORALL.view(), 2)
                &&& forall_args.len() == 2
                &&& forall_args[0] matches SpecTerm::App(f2, member_args)
                &&& f2 == SpecFnName::User(FN_NAME_MEMBER.view(), 2)
                &&& member_args.len() == 2

                &&& member_args[0] matches SpecTerm::Var(loop_var)
                &&& member_args[1].as_list() matches Some(list)

                // Then the proof obligation is that
                // for each i in 0..list.len(), subproofs[i] is a proof of <Goal>[X |-> list[i]]
                &&& subproofs.len() == list.len()
                &&& forall |i| 0 <= i < list.len()
                    ==> (#[trigger] subproofs[i]).stmt == forall_args[1].subst(SpecSubst(map!{ loop_var => list[i] }))
            }

            SpecProof::ForallBase(subproofs) => {
                // self.stmt is of the form forall(t1, t2)
                &&& self.stmt matches SpecTerm::App(SpecFnName::User(name, arity), args)
                &&& args.len() == arity
                &&& name == FN_NAME_FORALL.view()
                &&& arity == 2

                // For all rules, either
                // - the rule is a fact and matches the predicate
                // - the head of the rule is not unifiable with the predicate
                //
                // NOTE: there might be terms in between (i.e. unifiable but not matching)
                // we enforce the absence of these case for a simpler spec
                //
                // TODO: maybe extend this to full unification?
                &&& forall |i| 0 <= i < program.rules.len() ==> {
                    ||| (#[trigger] program.rules[i]).body.len() == 0 &&
                        args[0].matches(program.rules[i].head).is_some()
                    ||| args[0].not_unifiable(program.rules[i].head)
                }

                // First filter rules to those that match the predicate
                // then check that each filtered rule has the correct proof
                &&& filter_map(program.rules, |rule: SpecRule| {
                    if let Some(subst) = args[0].matches(rule.head) {
                        Some(args[1].subst(subst))
                    } else {
                        None
                    }
                }) =~= subproofs.map_values(|thm: SpecTheorem| thm.stmt)

                // &&& {
                //     let matched_rules = program.rules.filter(|rule: SpecRule| args[0].matches(rule.head));
                
                //     &&& matched_rules.len() == subproofs.len()

                //     // For each matched fact against t1, the corresponding subproof
                //     // should be t2 applied to the matching substitution 
                //     &&& forall |i| #![trigger matched_rules[i]]
                //         0 <= i < matched_rules.len() ==>
                //         // Exists a substitution `subst` such that
                //         // P[subst] = head of the rule
                //         // Q[subst] = subproof
                //         (exists |subst: SpecSubst|
                //             #[trigger] args[0].subst(subst) == matched_rules[i].head &&
                //             args[1].subst(subst) == subproofs[i].stmt)
                // }
            }

            // Specifications for the built-in functions
            SpecProof::BuiltIn => {
                // self.stmt is of the form f(...) where f is a domain function
                &&& self.stmt matches SpecTerm::App(SpecFnName::User(name, arity), args)
                &&& args.len() == arity
                &&& {
                    ||| {
                        &&& (name == FN_NAME_EQ.view() || name == FN_NAME_EQUIV.view())
                        &&& arity == 2
                        &&& args[0] == args[1]
                    }
                    ||| {
                        &&& (name == FN_NAME_NOT_EQUIV.view())
                        &&& arity == 2
                        &&& args[0] != args[1]
                    }
                    ||| {
                        &&& name == FN_NAME_LENGTH.view()
                        &&& arity == 2
                        &&& args[0].as_list() matches Some(list)
                        &&& args[1] matches SpecTerm::Literal(SpecLiteral::Int(len))
                        &&& list.len() == len
                    }
                    ||| {
                        &&& name == FN_NAME_MEMBER.view()
                        &&& arity == 2
                        &&& true
                    }
                    ||| {
                        // Base case for negation
                        // If the term is not unifiable with any rule head
                        // then the negation of the term holds
                        &&& name == FN_NAME_NOT.view()
                        &&& args.len() == 1
                        
                        // NOTE: this might be innefficient to check if implemented naively
                        &&& forall |i| 0 <= i < program.rules.len() ==>
                            (#[trigger] program.rules[i]).head.not_unifiable(args[0])
                    }
                }
            }
        }
    }
}

}
