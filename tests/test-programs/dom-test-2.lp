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
node(2..3).
&dom {(-2-5)..1+(-7); 7+(-1)..(5+2)} = at(X) :- node(X).

