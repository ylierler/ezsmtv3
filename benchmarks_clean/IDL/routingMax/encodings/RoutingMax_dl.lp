% reachtime is >= 0 

%cspvar(at(X),0,T) :- node(X), critical(Y,T).
&dom{0..T}=at(X):- node(X), critical(Y,T).
&dom {0;P} = p(X,Y) :- edge(X,Y,D,P).

% initial node is reached at 0.
reach(X) :- init(X).
&diff {at(X)} = 0 :- init(X).

% nodes reached later than the delay
reach(Y) :- reach(X), route(X,Y). 
&diff {at(Y) - at(X)} >= D :- route(X,Y), edge(X,Y,D,P).

% critical nodes have to be reached in time
:- critical(X,T), not reach(X).
:- critical(X,T), reach(X), &diff {at(X)}>T.

% any edge can be in the route
{route(X,Y)} :- edge(X,Y,D,P). 

% one incoming/outgoing edge for each node
:- route(X,Y1), route(X,Y2), node(X), node(Y1), node(Y2), Y1!=Y2. 
:- route(X1,Y), route(X2,Y), node(Y), node(X1), node(X2), X1!=X2.

%sum up profits
&diff {p(X,Y)} =0 :-edge(X,Y,D,P), not route(X,Y).
&diff {p(X,Y)} =P :-edge(X,Y,D,P), route(X,Y).
:- #sum {P,X,Y,D : edge(X,Y,D,P), route(X,Y) } < 620.
