good(f(a)).

hmm(f(_), f(_)).

test(X, Y) :-
    hmm(X, Y),
    good(X).

go :- test(f(X), f(X)).
