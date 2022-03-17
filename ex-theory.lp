#theory difference {
    constant    { - : 0, unary  };
    diff_term   { - : 0, binary, left };

    &required/0 : diff_term, {<=,>=,<,>}, constant, any
}.

a :- not b.
b :- not a.
e :- a, b.
e :- not a, not b.

&required { x } >= 10 :- e.
&required { x } <= 9 :- not e.
