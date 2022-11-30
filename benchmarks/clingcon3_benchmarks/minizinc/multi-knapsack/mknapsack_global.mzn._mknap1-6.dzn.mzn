%------------------------------------------------------------------------------%
% Multi Dimensional Knapsack Problem
%------------------------------------------------------------------------------%

include "knapsack.mzn";

%------------------------------------------------------------------------------%
% Parameters

int: N; % number of variables
int: M; % number of constraints

set of int: VRange = 1..N;
set of int: CRange = 1..M;

array[CRange,VRange] of int: a;     % Weight of items per bin
array[CRange] of int: b;            % Sizes of bins
array[VRange] of int: c;            % Profit of items

%------------------------------------------------------------------------------%
% Ignored parameters

int: z;                             % Normally the optimal value

%------------------------------------------------------------------------------%
% Variables

array[VRange] of var 0..1: x;               % Whether an item is packed
array[CRange] of var 0..ub_array(b): bVar;  % Total weight in a bin

var 0..sum(c): objective = sum(i in VRange)(c[i] * x[i]);   % Total profit

%------------------------------------------------------------------------------%
% Constraints

    % Constraining the size of the bins
    %
constraint
	forall(i in CRange)( bVar[i] >= 0 /\ bVar[i] <= b[i] );

    % Knapsack constraints
    %
constraint
	forall(i in CRange)( 
        knapsack([a[i,j] | j in VRange], c, x, bVar[i], z) 
    );  

%------------------------------------------------------------------------------%
% Some integrety check for the (input) data

constraint 
    forall(i in CRange,j in VRange)(
        assert(a[i,j] >= 0, "negative values in a") 
    );
constraint 
    forall(i in CRange)( assert(b[i] >= 0, "negative values in b") );
constraint 
    forall(j in VRange)( assert(c[j] >= 0, "negative values in c") );
constraint assert(z >= 0, "negative z");

%------------------------------------------------------------------------------%
% Search

solve 
    :: int_search(x, input_order, indomain_max, complete)
    maximize objective;

%------------------------------------------------------------------------------%
% Output

output [ 
    "x = ", show(x), ";\n",
    "objective = ", show(objective), ";\n"
];

%------------------------------------------------------------------------------%
N=50;
M=5;

z=16537;
c=[560, 1125, 300, 620, 2100, 431, 68, 328, 47, 122, 322, 196, 41, 25, 425, 4260, 416, 115, 82, 22, 631, 132, 420, 86, 42, 103, 215, 81, 91, 26, 49, 420, 316, 72, 71, 49, 108, 116, 90, 738, 1811, 430, 3060, 215, 58, 296, 620, 418, 47, 81];

b=[800, 650, 550, 550, 650];
a=[|
40, 91, 10, 30, 160, 20, 3, 12, 3, 18, 9, 25, 1, 1, 10, 280, 10, 8, 1, 1, 49, 8, 21, 6, 1, 5, 10, 8, 2, 1, 0, 10, 42, 6, 4, 8, 0, 10, 1, 40, 86, 11, 120, 8, 3, 32, 28, 13, 2, 4|
16, 92, 41, 16, 150, 23, 4, 18, 6, 0, 12, 8, 2, 1, 0, 200, 20, 6, 2, 1, 70, 9, 22, 4, 1, 5, 10, 6, 4, 0, 4, 12, 8, 4, 3, 0, 10, 0, 6, 28, 93, 9, 30, 22, 0, 36, 45, 13, 2, 2|
38, 39, 32, 71, 80, 26, 5, 40, 8, 12, 30, 15, 0, 1, 23, 100, 0, 20, 3, 0, 40, 6, 8, 0, 6, 4, 22, 4, 6, 1, 5, 14, 8, 2, 8, 0, 20, 0, 0, 6, 12, 6, 80, 13, 6, 22, 14, 0, 1, 2|
8, 71, 30, 60, 200, 18, 6, 30, 4, 8, 31, 6, 3, 0, 18, 60, 21, 4, 0, 2, 32, 15, 31, 2, 2, 7, 8, 2, 8, 0, 2, 8, 6, 7, 1, 0, 0, 20, 8, 14, 20, 2, 40, 6, 1, 14, 20, 12, 0, 1|
38, 52, 30, 42, 170, 9, 7, 20, 0, 3, 21, 4, 1, 2, 14, 310, 8, 4, 6, 1, 18, 15, 38, 10, 4, 8, 6, 0, 0, 3, 0, 10, 6, 1, 3, 0, 3, 5, 4, 0, 30, 12, 16, 18, 3, 16, 22, 30, 4, 0|];
