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
&sum {x} > 5 :- a.
:- &sum {x,2 : a} > 10.

% (declare-const |a| Bool)
% (assert (ite |a| (> (+ x) 5))
% (assert (not (> (+ x) 10)))

% 10 = t1
% 5 = t4
% sum = t0
% x = t3
% > = t2
% ta0 = t3 = x
% a1 = t0 ta0 t2 t1 = sum x > 10
% a3 = t0 ta0 t2 t4 = sum x > 5

%% employee(0..3).
%% shift(0,0,2).
%% shift(1,0,5).
%% shift(2,1,3).
%% shift(3,6,12).
%% shift(4,5,10).
%% shift(5,6,10).
%% shift(6,4,10).
%% shift(7,8,12).
%% shift(8,9,11).
%% shift(9,11,12).
%% shift(10,9,12).


%% { shiftAssignment(S,E) : employee(E) } <= 1 :- shift(S,_,_).


%% :-  shiftAssignment(S1,E),
%%     shiftAssignment(S2,E),
%%     S1 != S2, % Optimization over !=
%%     shift(S1,Shift1Start,Shift1End,_),
%%     shift(S2,Shift2Start,Shift2End,_),
%%     Shift1Start < Shift2End,
%%     Shift2Start < Shift1End.
