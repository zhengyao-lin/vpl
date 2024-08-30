edge(a, b).
edge(a, c).
edge(a, d).

good(X) :- perfect(X).
good(X) :- not_bad(X).

perfect(b).
not_bad(c).
not_bad(d).

go :- forall(edge(a, X), good(X)).
