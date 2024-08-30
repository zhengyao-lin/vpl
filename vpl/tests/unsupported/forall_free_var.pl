good(2).

go :- Y is 4, forall(good(X), (Y is X * 2, Y =< 10)).
