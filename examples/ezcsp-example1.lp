#theory qf_lia {
    linear_term {
        + : 5, unary;
        - : 5, unary;
        * : 4, binary, left;
        + : 3, binary, left;
        - : 3, binary, left
    };

    dom_term {
        + : 5, unary;
        - : 5, unary;
        .. : 1, binary, left
    };

    &dom/0 : dom_term, {=}, linear_term, any;
    &sum/0 : linear_term, {<=,=,>=,<,>,!=}, linear_term, any
}.

d(1..2).
&dom {10..20} = v(X) :- d(X).
&sum {v(1)} >= v(2).
&sum {v(X) : d(X)} >= 39.

&dom {20..40} = s.
&sum {v(X) : d(X)} = s.
