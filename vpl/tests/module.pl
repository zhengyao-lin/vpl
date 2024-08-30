:- module(test, [ go/0, edge/2 ]).

edge(a, b).

go :- edge(a, b).
