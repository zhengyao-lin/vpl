good(a).
good(b).
good(c).

go :- forall(member(X, [a, b, c]), good(X)).
