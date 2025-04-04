
% Select edges for the cycle
 { cycle(X,Y) } :- edge(X,Y), vtx(X).
 { cycle(X,Y) } :- edge(Y,X), vtx(X).
:-cycle(X,Y1),cycle(X,Y2),vtx(X),Y1!=Y2.
existX(X):-vtx(X), cycle(X,Y).
:-not existX(X),vtx(X).

 { cycle(X,Y) } :- edge(X,Y), vtx(Y).
 { cycle(X,Y) } :- edge(Y,X), vtx(Y).
:-cycle(X1,Y),cycle(X2,Y),vtx(Y),X1!=X2.
existY(Y):-vtx(Y), cycle(X,Y).
:-not existY(Y),vtx(Y).

reached(X) :- bound(X).
reached(Y) :- reached(X), cycle(X,Y).

:- vtx(X), not reached(X).

cost(X,Y,C) :- edgewt(X,Y,C).
cost(X,Y,C) :- edgewt(Y,X,C), { edgewt(X,Y,D) : edgewt(X,Y,D) } 0.

% Weight constraint on the Hamiltonian cycle
%:- W+1 [ cycle(X,Y) : cost(X,Y,C) = C ], maxweight(W).
&dom {0;C} = c(X,Y) :- cost(X,Y,C).
&sum {c(X,Y)} =0 :-cost(X,Y,C), not cycle(X,Y).
&sum {c(X,Y)} =C :-cost(X,Y,C), cycle(X,Y).
:- &sum {c(X,Y):cost(X,Y,C)} > W, maxweight(W).

% Symmetry breaking: Reach "smaller" neighbor from starting node
% (assumes symmetric costs for both directions of an edge!)
:- bound(X), cycle(Y,X), cycle(X,Z), Y < Z.

