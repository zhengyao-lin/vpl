good(a).
good(b).
good(c).

not_bad(a).
not_bad(b).
not_bad(c).

go :- forall(member(X, [a, b, c]), (good(X), not_bad(X))).
