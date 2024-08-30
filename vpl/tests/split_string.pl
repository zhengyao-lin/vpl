
go :-
    split_string("a,b,c", ",", "", ["a", "b", "c"]),
    split_string("a|b|c", "|", "", ["a", "b", "c"]),
    split_string("", ",", "", [""]),
    split_string(",", ",", "", ["", ""]).
