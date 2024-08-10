edge(a, b).
edge(a, c).
edge(a, d).

good(b).
good(c).
good(d).

go :- findall(X, edge(a, X), List), forall(member(Y, List), good(Y)).
