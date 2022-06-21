% http://smtlib.cs.uiowa.edu/logics-all.shtml#QF_LIA
% https://www.cs.uni-potsdam.de/~torsten/Potassco/Slides/tsolving.pdf
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

{a}.
:- &sum {x + 2} > (1 + (3  + y)) + 5.
