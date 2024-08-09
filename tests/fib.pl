mul(0, _, 0).
mul(s(X), Y, Z) :- mul(X, Y, W), add(Y, W, Z).

add(0, X, X).
add(s(X), Y, Z) :- add(X, s(Y), Z).

% fib(N, F): F is the N-th Fibonacci number
fib(0, 0).
fib(s(0), s(0)).
fib(s(s(N)), F) :- fib(s(N), F1), fib(N, F2), add(F1, F2, F).

% Compute fib(9)
go :- X = s(s(s(0))), mul(X, X, Y), fib(Y, _).
