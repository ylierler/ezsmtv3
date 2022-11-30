% ezcsp --mkatoms --bprolog domain-lp.ez inst-ijcai-lin7.ez output.ez plan.ez general.ez generate.ez refuel.ez

%%%%%%%%%%%%%%%%%% problem instance
% Generator problem with 7 refuel tanks
%

step(0..3).

duration(generate,1000).
%maction(generate).

maxintval(RT) :- duration(generate,RT).

tankcap(1000).
tanklv(880).

refuel_tank(tank1).
refuel_tank(tank2).
refuel_tank(tank3).
refuel_tank(tank4).
refuel_tank(tank5).
refuel_tank(tank6).
refuel_tank(tank7).
cap(T,20) :- refuel_tank(T).
duration(refuel(T),10) :- refuel_tank(T).

%maction(refuel(TK)) :- refuel_tank(TK).



