edge(a, b).
edge(a, c).
edge(a, d).

good(b).
good(c).
good(d).

go :- forall(edge(a, X), good(X)).
