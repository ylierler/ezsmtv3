#const red=0. % alternatives: x, y, z

redundant(x) :- red = x : red != z.
redundant(y) :- red = y : red != z.

size(x,R,X) :- rectangle(R,X,Y).
size(y,R,Y) :- rectangle(R,X,Y).

large(S)     :- S = #max{ X*Y : rectangle(R,X,Y) }, S != #inf.
large(S/Z,Z) :- large(S), Z = #max{ Y : rectangle(R,X,Y), S = X*Y }.
break(M)     :- large(X,Y), M = #min{ R : rectangle(R,X,Y) }.
divide(R,2)  :- break(R).
divide(R,1)  :- rectangle(R,X,Y), not break(R).

height(M) :- M = #max{ Y : rectangle(R,X,Y) }.
bound(B)  :- S = #sum{ X*Y,R : rectangle(R,X,Y) }, width(W), height(M),
             N = (S+W-1)/W, B = (M+N+|M-N|)/2.

false :- bound(B), maxheight(H), H < B.
false :- size(x,R,X), width(W), W < X.
:- false.

range(x,R,N)   :- size(x,R,X), divide(R,D), width(W), N = (W-X)/D, 0 < N, not false.
range(y,R,N)   :- size(y,R,Y), divide(R,D), maxheight(H), N = (H-Y)/D, 0 < N, not false.
range(A,R,N-1) :- range(A,R,N), 1 < N.

{ geq(A,R,N) } :- range(A,R,N).
:- geq(A,R,N), not geq(A,R,N-1), 1 < N.

position(A,R,0) :- size(A,R,S), not geq(A,R,1).
position(A,R,N) :- geq(A,R,N), not geq(A,R,N+1).

beyond(A,R1,R2,N) :- size(A,R1,S), geq(A,R2,N), not geq(A,R1,N-S+1), R1 != R2, S <= N,
                     rectangle(R1,X,Y), A = y : rectangle(R2,X,Y), R2 < R1, not redundant(y).
beyond(A,R1,R2)   :- beyond(A,R1,R2,N).
beyond(R1,R2)     :- beyond(A,R1,R2),
                     rectangle(R1,X,Y), A = x : rectangle(R2,X,Y), R2 < R1.
:- rectangle(R1,X1,Y1), rectangle(R2,X2,Y2), R1 < R2,
   not beyond(R1,R2), not beyond(R2,R1) : (X1,Y1) != (X2,Y2).
:- rectangle(R1,X,Y), rectangle(R2,X,Y), R1 < R2, beyond(y,R2,R1).
% :- beyond(A,R1,R2), beyond(A,R2,R1).

% mark(M) :- geq(y,R,N), size(y,R,Y), bound(B), M = N+Y-B, 0 < M.
% :~ mark(N). [1,N]
:~ geq(y,R,N), size(y,R,Y), bound(B), M = N+Y, B < M. [1,M]
:~ bound(B). [1,1..B]

#show position/3.

% Redundant constraints

untouch(A,R1,R2) :- size(A,R1,S), geq(A,R2,N), not geq(A,R1,N-S), R1 != R2, S < N, redundant(A),
                    rectangle(R1,X,Y), R1 < R2 : rectangle(R2,X,Y).

touch(x,R2) :- size(x,R1,X1), size(x,R2,X2), R1 != R2, width(W), X1+X2 <= W, redundant(x),
               not untouch(x,R1,R2), not beyond(y,R1,R2),
               not beyond(R2,R1) : not rectangle(R2,X,Y);
               rectangle(R1,X,Y), R1 < R2 : rectangle(R2,X,Y).
touch(y,R2) :- size(y,R1,Y1), size(y,R2,Y2), R1 != R2, maxheight(H), Y1+Y2 <= H, redundant(y),
               not untouch(y,R1,R2), not beyond(x,R1,R2),
               not beyond(R2,R1),
               rectangle(R1,X,Y), R1 < R2 : rectangle(R2,X,Y).
:- geq(A,R,1), not touch(A,R), redundant(A).
