edge(a, [a, b]).
edge(a, [b, b, a]).
edge(a, [c, a, d, e]).

go :- forall(edge(a, X), member(a, X)).
