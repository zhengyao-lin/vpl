Certified Prolog
---

## Usage

To compile, run `make`, which will produce an executable at `target/debug/vpl`.

To run queries, use the following command:
```
target/debug/vpl <Prolog source file> <entry query>
```

This will produce a list of intermediate goals that have been validated in the verified kernel.
For example, consider the following Prolog program:
```
node(n0).
node(n1).
node(n2).
node(n3).
node(n4).
edge(n3, n4).
edge(n2, n3).
edge(n1, n2).
edge(n0, n1).
connected(X, Y) :- edge(X, Y).
connected(A, B) :- edge(A, M), connected(M, B).
go :- connected(n0, n4).
```

The output of `vpl` is:
```
validated: edge(n0, n1)
validated: edge(n1, n2)
validated: edge(n2, n3)
validated: edge(n3, n4)
validated: connected(n3, n4)
validated: connected(n2, n4)
validated: connected(n1, n4)
validated: connected(n0, n4)
validated: go
```
Each line `validated: <Goal>` indicates that a proof of `<Goal>` has been validated in the verified kernel.

## Validation pipeline

Given a source Prolog program and an entry goal `goal`, the Prolog program is first parsed to create an in-memory representation for proof checking.

We then run `swipl` on the Prolog program along with a meta-interpreter (`prolog/meta.pl`) to solve the goal `prove(goal)`.

The meta-interpreter will output a trace, describing intermediate results and the relationship between them (essentially a Hilbert-style proof).
For the example above, the trace looks like this:
```
0. edge(n0,n1) by apply(fact, 9)
1. edge(n1,n2) by apply(fact, 8)
2. edge(n2,n3) by apply(fact, 7)
3. edge(n3,n4) by apply(fact, 6)
4. connected(n3,n4) by apply(3, 10)
5. connected(n2,n4) by apply([2,4], 11)
6. connected(n1,n4) by apply([1,5], 11)
7. connected(n0,n4) by apply([0,6], 11)
8. go by apply(7, 12)
```
The apply tactic is read as `apply(subgoals, line number of the clause)`.

Our tool then parses this trace and uses a verified kernel to check its validity against the specification of well-formed proofs in `src/proof.rs`.

## What am I trusting

The idea is to reduce the trusted parts to:
1. The specification of the kernel in `src/proof.rs`,
which describes the proof rules allowed to construct valid goals (e.g. clause application, built-in function evaluation for strings and lists).
2. The Prolog parser (`src/parser.rs`), which should accurately parse the input Prolog program.

The rest of the tool, including SWI-Prolog, does not need to be trusted.

## Missing features

TODO:

- [x] Integers
- [x] Strings
- [x] Lists
- [x] Some built-in functions for strings, lists
- [x] Arithmetic
- [x] Disjunction `;`
- [x] Anonymous variables
- [x] Nested conjunctions and disjunctions
- [x] `forall(member(X, L), ..)`
- [x] `\+base_pred(..)`
- [x] `forall(base_pred(...), ..)`
- [x] `findall(X, base_pred(..., X), ..)`
- [ ] Handle the module system better when loading files
- [ ] Private clauses in modules
- [ ] Adapt to optimizations done by the compiler
- [ ] Right now we conflate atom and nullary applications (e.g. `hey` vs `hey()`); need to fix this
- [ ] More error messages for failed validation
