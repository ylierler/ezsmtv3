#const n = 8.

% n-Queens encoding

{ q(I,1..n) } == 1 :- I = 1..n.
{ q(1..n,J) } == 1 :- J = 1..n.
:- { q(D-J,J) } >= 2, D =   2..2*n.
:- { q(D+J,J) } >= 2, D = 1-n..n-1.% instance

% 1 0 1 17 1 2 2 18 1 19 1
% 1 2 2 18 1 19 1

% never :- { q(1,7), q(2,7) } >= 2
