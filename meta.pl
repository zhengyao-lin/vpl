% A meta-interpreter for Prolog that outputs a Hilbert-style proof trace.
% To use, run the desired goal with `prove(Goal)`.

:- nb_setval(proof_id, 0).

gen_id(Id) :-
    nb_getval(proof_id, Id),
    NewId is Id + 1,
    nb_setval(proof_id, NewId).

% Log a proof step
log_proof(Id, Goal) :-
    write(Id), write(". "),
    writeq(Goal),
    write(" by ").

% Helper function for prove(maplist(...), ...)
prove_map(Fn, X, Y) :-
    % Construct a new term Fn(X, Y)
    Term =.. [Fn, X, Y],
    prove(Term).

% prove(Goal, Id) tries to prove Goal and if success,
% the proof that Goal is true is associated with node Id
prove(true, fact) :- !.

prove((A, B), [Id1, Id2]) :- !,
    prove(A, Id1),
    prove(B, Id2).
    % gen_id(Id),
    % log_proof(Id, (A, B)),
    % write("and("), write(Id1), write(", "), write(Id2), writeln(")").

prove((A; B), Id) :- !,
    (prove(A, Id1), gen_id(Id), log_proof(Id, (A;B)), write("or_left("), write(Id1), writeln(")");
     prove(B, Id2), gen_id(Id), log_proof(Id, (A;B)), write("or_right("), write(Id2), writeln(")")).

% Special case for maplist
prove(maplist(Fn, List, Results), Id) :-
    !,
    maplist(prove_map(Fn), List, Results),
    gen_id(Id),
    log_proof(Id, maplist(Fn, List, Results)),
    writeln("maplist").

% Builtin predicates
prove(Goal, Id) :-
    % predicate_property(Goal, P),
    % write(Goal), write(", "), writeln(P),
    (
        predicate_property(Goal, built_in);
        predicate_property(Goal, autoload(_))
    ),
    !,
    Goal,
    gen_id(Id),
    log_proof(Id, Goal),
    writeln("built-in").

% Otherwise we try user-defined rule application
prove(Goal, Id) :-
    % \+(predicate_property(Goal, built_in); predicate_property(Goal, meta_predicate(_))),
    clause(Goal, Body, Ref),
    prove(Body, BodyId),

    % Get clause information
    clause_property(Ref, file(File)),
    clause_property(Ref, line_count(Line)),

    % Include file and line number of the rule applied
    gen_id(Id),
    log_proof(Id, Goal),
    write("apply("), write(BodyId), write(", "),
    write(File), write(":"), write(Line),
    writeln(")").

prove(Goal) :-
    prove(Goal, _).
