% There is some optimization going on
% if we use good(X) :- X = a. (will be translated into good(a))

good(X) :- X == a.
good(X) :- X == b.
good(X) :- [1,2,X] = [1,2|[c]].

go :- forall(member(X, [a, b, c]), good(X)).
