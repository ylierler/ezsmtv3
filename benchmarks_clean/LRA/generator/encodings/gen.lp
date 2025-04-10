
%%%%%%%%%%%%%%%%%% general
%

% fluents: quant: start(I), end(I)
%cspvar(start(I),0,MI) :- step(I), maxintval(MI).
%cspvar(end(I),0,MI) :- step(I), maxintval(MI).
&sum {start(I)}>=0 :- step(I).
&sum {end(I)}>=0 :- step(I).

% start(I+1) == end(I) for every step I
&sum {start(I2); -1*end(I1)}=0 :- step(I1), step(I2), I2=I1+1.
&sum {end(I); -1*start(I)}>=0 :- step(I).%%%%%%


% inertia
holds(F,I2) :-
	fluent(F),
	step(I1), step(I2), I2=I1+1,
	holds(F,I1),
	not hold_s(F,I2).

hold_s(F,I2) :-
	fluent(F),
	step(I1), step(I2), I2=I1+1,
	hold_s(F,I1),
	not holds(F,I2).

% fluents: quant: v_initial(fuel_level), v_final(fuel_level)
&sum {v_initial(fuel_level,I)}>=0 :- step(I).
&sum {v_initial(fuel_level,I)}<=TC :- step(I), tankcap(TC).

&sum {v_final(fuel_level,I)}>=0 :- step(I).
&sum {v_final(fuel_level,I)}<=TC :- step(I), tankcap(TC).


% v_initial(fuel_level,I+1)=v_final(fuel_level,I)
&sum {v_initial(fuel_level,I2); -1*v_final(fuel_level,I1)}=0 :-
	step(I1), step(I2), I2=I1+1.


% fuel_level is changed by the respective contributions
%

% sum of the increments
&sum {v(contrib(fuel_level,incr),I)}>=0 :- step(I).
incr(I,v(contrib(fuel_level,incr,SRC),I)) :-
	step(I),
	v(contrib(fuel_level,incr,SRC),I).
% required(sum([incr(I)/2],==,v(contrib(fuel_level,incr),I))) :- step(I).
&sum {incr(I,v(contrib(fuel_level,incr,SRC),I)): step(I), v(contrib(fuel_level,incr,SRC),I); -1*v(contrib(fuel_level,incr),I)}=0 :- step(I).

% sum of the decrements
&sum {v(contrib(fuel_level,decr),I)}>=0 :- step(I).
decr(I,v(contrib(fuel_level,decr,SRC),I)) :-
	step(I),
	v(contrib(fuel_level,decr,SRC),I).
% required(sum([decr(I)/2],==,v(contrib(fuel_level,decr),I))) :- step(I).
&sum {decr(I,v(contrib(fuel_level,decr,SRC),I)): step(I), v(contrib(fuel_level,decr,SRC),I); -1*v(contrib(fuel_level,decr),I)}=0 :- step(I).

% v_final(fuel_level,I)=v_initial(fuel_level,I) + v(contrib(fuel_level,incr)) - v(contrib(fuel_level,decr))
&sum {v_final(fuel_level,I); -1*v_initial(fuel_level,I); -1*v(contrib(fuel_level,incr),I); v(contrib(fuel_level,decr),I)}=0 :-
	step(I).



%%%%%%%%%%%%%%%%%% generate

% fluents: bool: inprogr(generate), quant: stime(generate), v(contrib(fuel_level,decr,generate))
fluent(inprogr(generate)).

fluent(generating).
hold_s(generating,0).	% this should really be specified in the problem instance. Being lazy here...

%cspvar(stime(generate),0,MI) :- maxintval(MI).
&sum {stime(generate)}>=0.
&sum {v(contrib(fuel_level,decr,generate),I)}>=0 :- step(I).

% actions: start(generate), end(generate)
action(start(generate)).
action(end(generate)).

% Because generate is durative, it must stop at some point after starting
1{ occurs(end(generate),I2) : step(I2) ,I2 > I1 , I2 < 3 }1 :-
	step(I1),
	occurs(start(generate),I1).
% workarond: clingcon does not handle the above choice rule if the set of choices is empty
:- cspdomain(clingcon), step(I1), occurs(start(generate),I1), I1>=3-1.

% generate cannot end if it isn't in progress
:- step(I),
   occurs(end(generate),I),
   hold_s(inprogr(generate),I).

% DURATION CONSTRAINT ON generate
% the time elapsed between start(generate) and end(generate) must be exactly what specified
&sum {end(I); -1*stime(generate)}=D :-
	step(I), duration(generate,D),
	occurs(end(generate),I).

completed(generate,I+1) :- 
	step(I), step(I+1),
	occurs(end(generate),I).


% start(generate) causes
% 	inprogr(generate)=true
%	stime(generate)=end(I)
holds(inprogr(generate),I2) :-
	step(I1), step(I2), I2=I1+1,
	occurs(start(generate),I1).

&sum {stime(generate); -1*end(I1)}=0 :-
	step(I1), step(I2), I2=I1+1,
	occurs(start(generate),I1).

% start(generate) causes
% 	generating=true
holds(generating,I2) :-
	step(I1), step(I2), I2=I1+1,
	occurs(start(generate),I1).

% end(generate) causes
% 	inprogr(generate)=false
%	????end(I)-stime(generate)==100?????
hold_s(inprogr(generate),I2) :-
	step(I1), step(I2), I2=I1+1,
	occurs(end(generate),I1).

% end(generate) causes
% 	generating=false
hold_s(generating,I2) :-
	step(I1), step(I2), I2=I1+1,
	occurs(end(generate),I1).


% MUST SEMANTICS
% --- see must-semantics.ez

% INERTIA for quant fluents, specialized to fuel_level for now
%

% v_final(fuel_level,I)=v_initial(fuel_level,I) by default
% v(contrib(fuel_level,decr,generate)) is 0 by default
&sum {v(contrib(fuel_level,decr,generate),I)}=0 :-
	step(I),
	not ab(contrib(fuel_level,decr,generate),I).

% v(contrib(fuel_level,decr,generate),I)=1*(end(I)-start(I)) if inprogr(generate)
ab(contrib(fuel_level,decr,generate),I) :-
	step(I),
	holds(inprogr(generate),I).

&sum {v(contrib(fuel_level,decr,generate),I); -1*(end(I)-start(I))}=0 :-
	step(I),
	holds(inprogr(generate),I).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Rules defining the must-semantics of process generate
% They are here, rather than in generate.ez, to make it easier to
% test alternative definitions.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% MUST SEMANTICS
1{ occurs(start(generate),I); required_false(geq_flevel_0,I) }1 :- step(I), I<3, hold_s(generating,I).
% numerical precondition
%required(v_final(fuel_level,I)>0) :- step(I), occurs(start(generate),I).	% does not work in domain-lp!!!!! and is also the wrong precondition
&sum {v_final(fuel_level,I)}>=0 :- step(I), occurs(start(generate),I).
% required_false
%required(v_final(fuel_level,I)<=0) :- step(I), required_false(geq_flevel_0,I).	% complement of v_final(fuel_level,I)>0
restricted_ineq(lp).
restricted_ineq(nlp).
&sum {v_final(fuel_level,I)}<0 :- cspdomain(DOM), not restricted_ineq(DOM), step(I), required_false(geq_flevel_0,I).	% for domain-fd
&sum {v_final(fuel_level,I)}<0 :- cspdomain(DOM), restricted_ineq(DOM), step(I), required_false(geq_flevel_0,I).	% for domain-lp

%%%%%%%%%%%%%%%%%% output formatting
%

% A is a macro action (maction) if
% actions start(A) and end(A) exist.
maction(A) :- action(start(A)), action(end(A)).

% quantitative fluent dur(I): duration of step (I)
&sum {dur(I)}>=0 :- step(I), maxintval(MI).
&sum {dur(I)}<=MI :- step(I), maxintval(MI).

&sum {dur(I); -1*end(I); start(I)}=0 :- step(I).


% quantitative fluent adur(A): duration of action A
&sum {adur(A)}>=0 :- maction(A), occurs(start(A),I1), occurs(end(A),I2), maxintval(MI).
&sum {adur(A)}<=MI :- maction(A), occurs(start(A),I1), occurs(end(A),I2), maxintval(MI).

&sum {adur(A); -1*end(I2); end(I1)}=0 :-
	step(I1), step(I2),
	maction(A),
	occurs(start(A),I1),
	occurs(end(A),I2).

% Special treatment for instantaneous actions
instoccurs(iact(A,I),I) :- instantaneous(A), occurs(A,I).

&sum {adur(iact(A,I))}>=0 :- instantaneous(A), occurs(A,I), maxintval(MI).
&sum {adur(iact(A,I))}<=MI :- instantaneous(A), occurs(A,I), maxintval(MI).
&sum {stime(iact(A,I))}>=0 :- instantaneous(A), occurs(A,I), maxintval(MI).
&sum {stime(iact(A,I))}<=MI :- instantaneous(A), occurs(A,I), maxintval(MI).
&sum {adur(iact(A,I))}=0 :-
	step(I),
	instantaneous(A),
	occurs(A,I).

&sum {stime(iact(A,I)); -1*end(I)}=0 :-
	step(I),
	instantaneous(A),
	occurs(A,I).

%%%%%%%%%%%%%%%%%% planner

%
% EXPERIMENTAL OBSERVATION
% For increased performance, plan.ez should be listed right after the
% problem instance.
%


% we are not equipped for multiple starts of generate
:- occurs(start(generate),I1), occurs(start(generate),I2), I1!=I2.

% planning: we can refuel, using each refuel tank at most once
0{ occurs(start(refuel(TK)),I) : step(I) }1 :- refuel_tank(TK).

% HEURISTIC: there should always be somme action between two states
% See below for its effect on performance.
some_action(I) :-
	step(I),
	occurs(_,I).
:- step(I), I < 3, not some_action(I).

%
% Similarly to the goal-related rules (see below),
% the following rule brings execution the time for 
% inst3-3.ez from ~70+sec to ~11sec in my experiments.
% The 1+-action-per-state heuristic (see above) brings
% execution time of inst3-3.ez further down to ~2sec.
%
completed(generate) :-
	step(I),
	completed(generate,I).

%
% ASP-style goal not needed
%   The goal below forces action generate to be completed.
%   However, other rules can be shown to guarantee that it will happen anyway:
%      1) the fact above forces generate to start at 0
%      2) the choice rule in generate.ez forcecs end(generate) to occur.
%
%   Removing the constraint below reduces execution time,
%   in inst3-3.ez, from ~70+sec to ~11sec in my experiments.
%   Removing the definition of goal_achieved/0 causes the time 
%   to go back up to ~70+sec again.
%
%
% GOAL
%goal_achieved(I) :- 
%	step(I),
%	completed(generate,I).
%
%goal_achieved :-
%	step(I),
%	goal_achieved(I).
%
%failed :- not goal_achieved.
%:- not goal_achieved.


%%%%%%%%%%%%%%%%%% refuel

% fluents: bool: inprogr(refuel(Tank)), quant: stime(refuel(Tank)), v(contrib(fuel_level,incr,refuel(Tank)))
fluent(inprogr(refuel(TK))) :- refuel_tank(TK).

%cspvar(stime(refuel(TK)),0,MI) :- maxintval(MI), refuel_tank(TK).
&sum {stime(refuel(TK))}>=0 :- refuel_tank(TK).
&sum {v(contrib(fuel_level,incr,refuel(TK)),I)}>=0 :- step(I), refuel_tank(TK).

% actions: start(refuel(Tank)), end(refuel(Tank))
action(start(refuel(TK))) :- refuel_tank(TK).
action(end(refuel(TK))) :- refuel_tank(TK).

% Because refuel is durative, it must end at some point after starting
1{ occurs(end(refuel(TK)),I2) : step(I2) ,I2>I1, I2 < 3 }1 :- 
	step(I), refuel_tank(TK),
	occurs(start(refuel(TK)),I1).

% refuel cannot end if it isn't in progress
:- step(I), refuel_tank(TK),
   occurs(end(refuel(TK)),I),
   hold_s(inprogr(refuel(TK)),I).

% DURATION CONSTRAINT ON refuel(TK)
% the time elapsed between start(refuel) and end(refuel) must be exactly what specified
&sum {end(I); -1*stime(refuel(TK))}=RT :-
	step(I), refuel_tank(TK), duration(refuel(TK),RT),
	occurs(end(refuel(TK)),I).

completed(refuel(TK),I+1) :- 
	step(I), step(I+1),
	refuel_tank(TK),
	occurs(end(refuel(TK)),I).


% start(refuel(TK)) causes
% 	inprogr(refuel(TK))=true
%	stime(refuel(TK))=end(I)
holds(inprogr(refuel(TK)),I2) :-
	step(I1), step(I2), I2=I1+1, refuel_tank(TK),
	occurs(start(refuel(TK)),I1).

&sum {stime(refuel(TK)); -1*end(I1)}=0 :-
	step(I1), step(I2), I2=I1+1, refuel_tank(TK),
	occurs(start(refuel(TK)),I1).

% end(refuel(TK)) causes
% 	inprogr(refuel(TK))=false
%	????end(I)-stime(refuel(TK))==10?????
hold_s(inprogr(refuel(TK)),I2) :-
	step(I1), step(I2), I2=I1+1, refuel_tank(TK),
	occurs(end(refuel(TK)),I1).

% contrib(fuel_level,refuel(TK)) is 0 by default
&sum {v(contrib(fuel_level,incr,refuel(TK)),I)}=0 :-
	step(I), refuel_tank(TK),
	not ab(contrib(fuel_level,incr,refuel(TK)),I).

% v(contrib(fuel_level,incr,refuel(TK)),I)=2*(end(I)-start(I)) if inprogr(refuel(TK))
ab(contrib(fuel_level,incr,refuel(TK)),I) :-
	step(I), refuel_tank(TK),
	holds(inprogr(refuel(TK)),I).

&sum{v(contrib(fuel_level,incr,refuel(TK)),I); -2*(end(I)-start(I))}=0 :-
	step(I), refuel_tank(TK),
	holds(inprogr(refuel(TK)),I).

%% start the clock at 0 for simplicity
&sum {start(0)}=0.



% initial state
%hold_s(inprogr(generate),0).
%hold_s(inprogr(refuel(TK)),0) :- refuel_tank(TK).
%&sum {v_initial(fuel_level,0)}=LV :- tanklv(LV).
