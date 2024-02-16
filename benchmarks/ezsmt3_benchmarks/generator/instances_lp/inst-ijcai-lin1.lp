% ezcsp --mkatoms --bprolog domain-lp.ez inst-ijcai-lin1.ez output.ez plan.ez general.ez generate.ez refuel.ez

%%%%%%%%%%%%%%%%%% problem instance
% Generator problem with 1 refuel tank
%


step(0..3).

duration(generate,1000).
%maction(generate).

maxintval(RT) :- duration(generate,RT).

tankcap(1000).
tanklv(990).

refuel_tank(tank1).
cap(T,20) :- refuel_tank(T).
duration(refuel(T),10) :- refuel_tank(T).

%maction(refuel(TK)) :- refuel_tank(TK).



