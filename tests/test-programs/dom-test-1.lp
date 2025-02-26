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

    &dom/0 : dom_term, {=}, linear_term, head;
    &logic/1 : linear_term, head
}.

&logic(lia).
node(0).
&dom {(-8)..(-6); (-2)..0; 5; 9..11} = at(X) :- node(X).
