concat([], L, L).
concat([H|T], L, [H|R]) :- 
    concat(T, L, R).

go :- concat([a, b, c], [d, e], [a, b, c, d, e]).

