% ezcsp --mkatoms --bprolog inst8.ez output.ez plan.ez general.ez moving.ez actions.ez

%%%%%%%%%%%%%%%%%% problem instance
%




step(0..3).

duration(moving,30).
uplimit(8).
downlimit(0).

maxintval(RT) :- duration(moving,RT).

% start the clock at 0 for simplicity
&sum {start(0)}=0.

% initial state
&sum {v_initial(d,0)}=0.
&sum {v(v,0)}=0.
hold_s(inprogr(moving),0).
holds(running,0).
