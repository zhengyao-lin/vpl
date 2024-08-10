% Some tests for syntactical equivalence \== and ==
go :-
    1 == 1, 1 \== 1 + 0, 1 \== 2,
    _ \== _, f(X) == f(X), f(X) \== f(Y), f(X) \== g(X), X \== Y,
    [1, 2, 3, 4] == [1, 2 | [3, 4]].
