%
% ezcsp --grounder gringo-3.0.5 --mkatoms --gams:knitro EXPERIMENT/init1 EXPERIMENT/instICAPS.ez EXPERIMENT/obs1 pioneerBasic.ez diag-min.ez
%

#const n=2.
#const curr_step=2.


% unexpected observation. It should have been 150
obs(v_final(x(r), 2),"80").
obs(v_final(y(r), 2),"0").
&sum {tend(2)}="59.01938237".

% HYPOTHESES (from diagnosis/instBasic1.ez)
ab(assumed_value,b_lvl(r)).

% the hypothesis on the value of b_lbl(r) returned by the diagnostic module is not retained
% because it causes issues within the constraint solver
%required(v_initial(b_lvl(r),0)=="0.53333349").
