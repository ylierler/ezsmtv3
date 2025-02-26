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
node(2..7).
&sum {4; (X+2*X); (3+1)*X; 5*2; X*X; -(2*2)-X} = at(X) :- node(X).
