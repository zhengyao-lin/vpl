a(X) :- member(X, [1, 2, 3]).
b(X) :- member(X, [4, 5]).

go :- forall(member(X, [1, 2, 3, 4, 5]), (a(X); b(X))).

% unsupported:
% go :- forall(member(X, [1, 2, 3, 4, 5]), (a(X); b(_))).
