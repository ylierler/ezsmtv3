%#include <csp>

#theory lp {
    lin_term {
    - : 2, unary;
    * : 1, binary, left;
    + : 0, binary, left;
    - : 0, binary, left
    };
    bounds{
    - : 4, unary;
    * : 3, binary, left;
    / : 2, binary, left;
    + : 1, binary, left;
    - : 1, binary, left;
    .. : 0, binary, left
    };

    &lp/0   : lin_term, {<=,>=,>,<,=,!=}, bounds, any;
    %&dom/0 : bounds, {=}, lin_term, head;
    &sum/0   : lin_term, {<=,>=,>,<,=,!=}, bounds, any
    %&objective/1 : lin_term, head;
    %&minimize/0 : lin_term, head;
    %&maximize/0 : lin_term, head
}.

% reachtime is >= 0 and <= maxTime
maxTime(M) :- M = #sum {D : edge(X,Y,D,P)}.
&dom {0..M} = at(X) :- node(X), maxTime(M).

% initial node is reached at 0.
reach(X) :- init(X).
&sum {at(X)} = 0 :- init(X).

% nodes reached later than the delay
reach(Y) :- reach(X), route(X,Y). 
&sum {at(Y); -1*at(X)} >= D :- route(X,Y), edge(X,Y,D,P).

% critical nodes have to be reached in time
:- critical(X,T), not reach(X).
:- critical(X,T), reach(X), &sum {at(X)}>T.

% any edge can be in the route
{route(X,Y)} :- edge(X,Y,D,P). 

% one incoming/outgoing edge for each node
:- route(X,Y1), route(X,Y2), node(X), node(Y1), node(Y2), Y1!=Y2. 
:- route(X1,Y), route(X2,Y), node(Y), node(X1), node(X2), X1!=X2.

%sum up profits
&sum {p(X,Y)} =0 :-edge(X,Y,D,P), not route(X,Y).
&sum {p(X,Y)} =P :-edge(X,Y,D,P), route(X,Y).
&sum {p(X,Y):edge(X,Y,D,P)} >= 620.
