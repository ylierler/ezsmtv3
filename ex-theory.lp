#theory difference {
    constant    { - : 0, unary  };
    diff_term   { - : 0, binary, left };
    linear_term { + : 2, unary; - : 2, unary;
                    * : 1, binary, left;
                    + : 0, binary, left; - : 0, binary, left };
    domain_term { .. : 1, binary, left };
    show_term   { / : 1, binary, left };

    &dom/0 : domain_term, {=}, linear_term, any;
    &sum/0 : linear_term, {<=,=,>=,<,>,!=}, linear_term, any;
    &diff/0 : diff_term, {<=}, constant, any;
    &show/0 : show_term, directive
}.

#const n=2.
#const m=1000.

task(1..n).
duration(T,200*T) :- task(T).
&dom {1..m} = start(T) :- task(T).
&dom {1..m} = end(T) :- task(T).
&diff { end(T) - start(T) } <= D :- duration(T,D).
&sum { end(T) : task(T); -start(T) : task(T) } <= m.
&show { start/1; end/1 }.

