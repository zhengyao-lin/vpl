
edge(a, b).
edge(b, c). % multiple facts for the condition of forall
edge(b, c).

good(b). % multiple facts for the body of forall
good(b).

good(c).

go :- forall(edge(a, X), good(X)), forall(edge(b, X), good(X)).
