%-----------------------------------------------------------------------------%
% Radiation problem, MiniZinc 2.0.4 version
%
%-----------------------------------------------------------------------------%

%-----------------------------------------------------------------------------%
% Parameters
%-----------------------------------------------------------------------------%

int: m;  % Rows
int: n;  % Columns

set of int: Rows    = 1..m;
set of int: Columns = 1..n;

	% Intensity matrix
array[Rows, Columns] of int: Intensity;


set of int: BTimes = 1..Bt_max;

int: Bt_max   = max(i in Rows, j in Columns) (Intensity[i,j]);
int: Ints_sum = sum(i in Rows, j in Columns) (Intensity[i,j]);

%-----------------------------------------------------------------------------%
% Variables
%-----------------------------------------------------------------------------%

	% Total beam-on time
var 0..Ints_sum: Beamtime;

	% Number of shape matrices
var 0..m*n: K;

	% N[b] is the number of shape matrices with associated beam-on time b
array[BTimes] of var 0..m*n: N;

	% Q[i,j,b] is the number of shape matrices with associated beam-on time
	% b that expose cell (i,j)
array[Rows, Columns, BTimes] of var 0..m*n: Q;

%-----------------------------------------------------------------------------%
% Constraints
%-----------------------------------------------------------------------------%

	% For FD/LP hybrid solving, all these should go the LP solver
	% (with a suitable linearisation of the 'max' expressions).
constraint
	Beamtime = sum(b in BTimes) (b * N[b])
	/\
	K = sum(b in BTimes) (N[b])
	/\
	forall(i in Rows, j in Columns)
		( Intensity[i,j] = sum([b * Q[i,j,b] | b in BTimes]) )
	/\
	forall(i in Rows, b in BTimes)
		( upper_bound_on_increments(N[b], [Q[i,j,b] | j in Columns]) );


predicate upper_bound_on_increments(var int: N_b, array[int] of var int: L) =
	N_b >= L[1] + sum([ max(L[j] - L[j-1], 0) | j in 2..n ]);
	%
	% Good linear version:
	% let { array[min(index_set(L))..max(index_set(L))] of var int: S } in
	% N_b >= L[1] + sum([ S[j] | j in 2..n ]) /\
	% forall([ S[j] >= L[j] - L[j-1] /\ S[j] >= 0 | j in 2..n ]);
	

%-----------------------------------------------------------------------------%
% Objective
%-----------------------------------------------------------------------------%
int: obj_min = lb((m*n + 1) * Beamtime + K);
int: obj_max = ub((m*n + 1) * Beamtime + K);
var obj_min..obj_max: objective = (m*n + 1) * Beamtime + K;

solve 
    :: int_search(
		[Beamtime] ++ N ++
	    	[Q[i,j,b] | i in Rows, j in Columns, b in BTimes ],
		input_order, indomain_split, complete)
	minimize objective;
		% really: (Beamtime, K),  i.e. in lexicographic order

%-----------------------------------------------------------------------------%

output [
	"objective = \(objective);\n",
    "Beamtime = \(Beamtime);\n",
    "K = \(K);\n",
    "N = \(N);\n",
    "Q = array3d(\(Rows), \(Columns), \(BTimes), \(Q));\n"
];

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

m = 14;	% rows
n = 14;	% columns

% max intensity = 9
Intensity = [|
7, 7, 0, 1, 8, 1, 5, 0, 2, 5, 0, 4, 5, 9 |
8, 7, 2, 8, 3, 9, 1, 8, 8, 3, 5, 4, 3, 6 |
4, 6, 7, 6, 6, 0, 1, 8, 1, 0, 4, 7, 0, 8 |
5, 1, 3, 3, 8, 0, 4, 0, 4, 9, 5, 3, 2, 1 |
3, 5, 5, 8, 2, 6, 1, 4, 7, 3, 6, 8, 7, 0 |
6, 1, 1, 3, 8, 1, 4, 2, 4, 9, 2, 2, 1, 4 |
0, 3, 6, 2, 4, 4, 4, 9, 5, 6, 6, 4, 4, 4 |
9, 3, 6, 8, 5, 0, 0, 6, 4, 2, 2, 2, 6, 0 |
0, 3, 6, 3, 3, 3, 1, 8, 6, 3, 9, 2, 7, 4 |
3, 5, 5, 0, 1, 9, 4, 4, 6, 5, 3, 0, 3, 4 |
3, 9, 6, 8, 7, 4, 1, 3, 9, 9, 8, 9, 1, 9 |
4, 3, 2, 2, 0, 0, 6, 6, 3, 5, 7, 6, 4, 4 |
1, 8, 7, 1, 3, 3, 7, 0, 4, 4, 3, 8, 2, 6 |
2, 6, 3, 7, 5, 5, 1, 2, 8, 5, 2, 0, 4, 2
|];

