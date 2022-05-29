#theory difference {
    constant    { - : 0, unary  };
    diff_term   { - : 0, binary, left };

    &required/0 : diff_term, {<=,>=,<,>}, constant, any
}.

a :- not b.
b :- not a.
e :- a, b.
e :- not a, not b.

{ task(X) } :- X = 1..5.

success :- &required { X } >= 10, task(X).
