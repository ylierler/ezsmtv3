%
% ezcsp --grounder gringo-3.0.5 --mkatoms --gams:knitro EXPERIMENT/init4 EXPERIMENT/instICAPS.ez EXPERIMENT/obs4 EXPERIMENT/goalICAPS.ez pl_heur.ez pioneerBasic.ez plan.ez
%

#const n=8.
#const curr_step=2.

% unexpected observation. It should have been 150
obs(v_final(x(r), 2),"80").
obs(v_final(y(r), 2),"0").
&sum {tend(2)}="40.33404215".
