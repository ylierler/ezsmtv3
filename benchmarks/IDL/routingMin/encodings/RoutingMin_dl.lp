%cspvar(at(X),0,T) :- node(X), critical(Y,T).
%&dom{0..T}=at(X):- node(X), critical(Y,T).

&diff {at(X)} <= T :- node(X), critical(Y,T).

% reachtime is >= 0 
&diff {at(X)}>= 0:- node(X).

% initial node is reached at 0.
reach(X) :- init(X).
&diff {at(X)} = 0 :- init(X).

% nodes reached later than the delay
reach(Y) :- reach(X), route(X,Y). 
&diff {at(Y) - at(X)} >= D :- route(X,Y), edge(X,Y,D).

% critical nodes have to be reached in time
:- critical(X,T), not reach(X).
:- critical(X,T), reach(X), &diff {at(X)}>T.

% any edge can be in the route
{route(X,Y)} :- edge(X,Y,D). 

% one incoming/outgoing edge for each node
:- route(X,Y1), route(X,Y2), node(X), node(Y1), node(Y2), Y1!=Y2. 
:- route(X1,Y), route(X2,Y), node(Y), node(X1), node(X2), X1!=X2.
