$domain(0..MV) :- max_total_weight(MV).
color(red).
color(blue).
color(green).

leaf(L) :- leafWeightCardinality(L,W,C).

% We mostly care about the lesser of weight and cardinality.
% Just call it leafWeight
leafCost(L,W) :- leaf(L), leafWeightCardinality(L,W,C), W <= C.
leafCost(L,C) :- leaf(L), leafWeightCardinality(L,W,C), C < W.

coloredPos(X) :- X=1..N-1, num(N).

% Each leaf will have a location in our sequence
location(X) :- X=0..N-1, num(N).

% Give each leaf a location in the sequence
1{ leafPos(L,N) : location(N) }1 :- leaf(L).

% No sharing locations
:- leafPos(L1, N), leafPos(L2, N), location(N), L1 != L2.


%%%% COLORS %%%%
% coloredPos(1) has a special case, look at locations 1 and 2 in leafPos to
% to determine color

% green if (weight(right) + card(right)) < (weight(left) + leafCost(right))
posColor(1,green) :- leafPos(L1,0), leafPos(L2,1), leafWeightCardinality(L1,WL,CL),
		leafWeightCardinality(L2,WR,CR), leafCost(L2,W3), W1=WR+CR, W2=WL+W3, W1 < W2.
% blue if not green and card(right) < weight(right)
posColor(1,blue) :- leafPos(L2,1), leafWeightCardinality(L2,W,C), C < W, 
		not posColor(1,green).
% red if not green and weight(right) < card(right)
posColor(1,red) :- leafPos(L2,1), leafWeightCardinality(L2,W,C), W <= C, 
		not posColor(1,green).

% Give each colored pos above 1 a unique color [****]
1{ posColor(P,N) : color(N) }1 :- coloredPos(P), P>1.


:- not posColor(N,green), N>1, coloredPos(N), leafPos(L,N), leafWeightCardinality(L,WR,CR),
 		nWeight(N-1)$> WR+CR-W2, leafCost(L,W2).
	
%%
%% PLACE for ADDON v1 or ADDON v2
%% tw.sequence++.sum-basis-addon-v2.con  ; tw.sequence++.sum-basis-addon-v1-moreseqallowed.con

%%%% WEIGHTS %%%%

% nWeight for first coloredPos
nWeight(1)$==W:- posColor(1,green), leafPos(L,1), leafWeightCardinality(L,WR,CR),
		W=WR+CR.
nWeight(1)$==W :- not posColor(1,green), leafPos(L1,0), leafPos(L2,1), 
		leafWeightCardinality(L1,WL,CL), leafCost(L2,WR), W=WL+WR.

% define nWeight/2
% green
nWeight(N)$==W :- coloredPos(N), N>1, posColor(N,green), leafPos(L,N), 
		leafWeightCardinality(L,WR,CR), W=WR+CR.

% not green
nWeight(N)$==nWeight(N-1)$+WR  :- coloredPos(N), N>1, not posColor(N,green), leafPos(L,N), 
		leafCost(L,WR).

$sum{ nWeight(P) : coloredPos(P) }$<=mv.

:- not posColor(N,blue), N>1, coloredPos(N), leafPos(L,N), leafWeightCardinality(L,W,C), C < W, 
nWeight(N-1)$<= W+C-W2, leafCost(L,W2).

%%
% If it's not  green and accords red color restrictions it must be red
:- not posColor(N,red), N>1, coloredPos(N), leafPos(L,N), leafWeightCardinality(L,W,C), C >= W,
nWeight(N-1)$<= W+C-W2, leafCost(L,W2).



%% + enforce sorted order of nongreen blocks
%%
:-not posColor(N,green), not posColor(N-1,green), coloredPos(N-1),
leafPos(L1,N-1),  leafPos(L2,N), leafCost(L1,C1), leafCost(L2,C2), C1>C2.

:-not posColor(N,green), not posColor(N-1,green), coloredPos(N-1),
leafPos(L1,N-1),  leafPos(L2,N), leafCost(L1,C), leafCost(L2,C), L1>L2.

%% ++ enforcing sorted green nodes (sorting by ids)
%%
:- leafPos(L1,P1),  leafPos(L2,P2), 
   posColor(P1,green), posColor(P2,green), 
   L1<L2, P1>P2.
