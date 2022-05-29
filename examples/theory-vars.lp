% https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_LIA/-/blob/master/cut_lemmas/10-vars/cut_lemma_01_001.smt2
%(set-info :smt-lib-version 2.6)
%(set-logic QF_LIA)

#theory QF_LIA {
    constant    { - : 0, unary  };
    diff_term   { - : 0, binary, left };
    linear_term { + : 2, unary; - : 2, unary;
                    * : 1, binary, left;
                    + : 0, binary, left; - : 0, binary, left };

    &var/0 : diff_term, directive;
    &diff/0 : diff_term, {<=,>=}, constant, any;
}

&var { x3 }.
&var { x4 }.
&var { x7 }.
&var { x8 }.

&diff { (x4 * 2) + ((x7 * -2) + (x8 * -2)) } >= 2.
