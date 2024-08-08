good(X) :- X == a.
good(X) :- X == b.
good(X) :- [1,2,X] = [1,2|[c]].

go :- forall(member(X, [a, b, c]), good(X)).
