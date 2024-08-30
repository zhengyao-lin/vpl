fact.

% true() should but doesn't work here since
% Prolog somehow replaces true() with true
% But we still distinguish them

go :- true, member(1, [1, 2, true]), true, fact.
