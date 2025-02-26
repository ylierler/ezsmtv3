#theory lp {
    linear_term {
    - : 2, unary;
    * : 1, binary, left;
    + : 0, binary, left;
    - : 0, binary, left
    };

    dom_term {
    - : 3, unary;
    + : 3, unary;
    * : 2, binary, left;
    + : 1, binary, left;
    - : 1, binary, left;
    .. : 0, binary, left
    };

    &sum/0   : linear_term, {<=,>=,>,<,=,!=}, linear_term, any;
    &logic/1 : linear_term, head
}.

&logic(lia).
node(6).
&sum {4; X; 10} = at(X) :- node(X).
