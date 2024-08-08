
concat(nil, L, L).
concat(cons(H, T), L, cons(H, R)) :- 
    concat(T, L, R).

go :- concat(
    cons(a, cons(b, nil)),
    cons(c, cons(d, cons(e, nil))),
    cons(a, cons(b, cons(c, cons(d, cons(e, nil)))))
).
