edge(X, X).

good(a).

go :- forall(good(X), edge(X, X)).
