% Model for mapping H263 encoder on a system with a network on chip (NoC)
%
% The model is a simplified version of the model presented in the paper
%
% "Mapping streaming applications on multiprocessors with time-division-multiplexed network-on-chip ",
% by
% Usman Mazhar Mirza, Flavius Gruian and Krzysztof Kuchcinski,
% Computers & Electrical Engineering, vol. 40, no. 8, pp. 276-291, 2014
%
% Author: Krzysztof Kuchcinski

include "globals.mzn";

int: row;          % number of rows in the mesh
int: col;          % number of columns in the mesh
int: k = row*col;  %  number processors
int: n = k + 2;    % number of nodes
int: no_links;     % number of links between processors
int: m = no_links + 2*k;  % number of arcs
int: no_flows;     % number of flows
int: link_bandwidth;

int: no_actors;

array[1..m, 1..2] of int: arc;

array[1..m] of int: unit_cost;

array[1..no_flows, 1..n] of int: balance;

int: processor_load;
array[1..k] of var 0..processor_load: cpu_loads;

array[1..no_actors] of int: actor_load;
array[1..2, 1..no_flows] of int: load;

array[1..no_flows] of var 0..10000: cost;

% var 0..10000: load_cost;
% var 0..10000: cpu_cost;
var 0..10000: communication_cost;
var 0..10000: objective;

array[1..2*no_flows] of var 1..k: flow_processor;

array[1..no_links] of var 0..link_bandwidth : comm_full;
array[1..k] of var 0..5*link_bandwidth : flow_from_processor;

array[1..k] of var 0..10000*no_flows: cc;

array[1..no_flows] of int: inStream;
array[1..no_flows, 1..n] of int: b;

array[1..no_flows, 1..k] of var 0..max(inStream): inFlow;
array[1..no_flows, 1..k] of var 0..max(inStream): outFlow;
array[1..no_flows, 1..no_links] of var 0..link_bandwidth: commFlow;

array[1..no_flows, 1..m] of var 0..max(max(inStream),link_bandwidth): flows;

array[1..no_flows,1..2] of int: source_destination_actor;

array[1..no_actors] of var 1..k: actor_processor;

array[1..2*k*no_flows + no_links] of var 0..max(max(inStream),link_bandwidth): total_flow;
array[1..2*k*no_flows + no_links] of int: total_unit_cost;
array[1..k+2*no_flows] of int: total_balance;

array[1..2*no_flows*k] of int: in_connections;
array[1..2*no_flows*k] of int: out_connections;
array[1..2*no_flows*k+no_links, 1..2] of int: all_connections;

%% === Model constraints ===

constraint %% constraining input and output flows defining mapping
   forall( i in 1..no_flows, j in 1..k) (inFlow[i,j] in {0, inStream[i]} /\ outFlow[i,j] in {0, inStream[i]})
;

constraint %% to select processor and not divide flow on incomming and outgoing streams
	forall (i in 1..no_flows) (count([flows[i,j] | j in 1..k], 0, k-1) /\ count([flows[i,j] | j in m-k+1..m], 0, k-1))
;

constraint %% network flow constraint
	forall (i in 1..no_flows) (network_flow_cost(arc,  [balance[i,j] | j in 1..n], unit_cost, [flows[i,j] | j in 1..m], cost[i]))
;

constraint  %% networkflow for all flows
	network_flow_cost(all_connections, total_balance, total_unit_cost, total_flow, communication_cost)
	/\
	%% flow for communications between processors for the combined network flow; must be the same as sum of separate flows
	forall (i in 1..no_links) (comm_full[i] = sum(j in 1..no_flows)(flows[j,i+k]))
;

constraint %% computes processors' load
	forall (i in 1..no_flows, j in 1..k) ( ( flows[i,j] != 0 <-> flow_processor[i] = j)
	       	     		               /\
				               ( flows[i, m-k+j] != 0 <-> flow_processor[no_flows+i] = j) )
	/\ 
	bin_packing_load(cpu_loads, flow_processor, [load[i, j] | i in 1..2, j in 1..no_flows])
;

constraint  %% cost function to minimize
	forall (i in 1..k) (cc[i] = sum(j in 1..no_flows)((flow_processor[source_destination_actor[j,1]] = i) * cost[j]))
	/\
	maximum(objective, [cpu_loads[i] + cc[i] | i in 1..k])
	% maximum(load_cost, [cpu_loads[i] + cc[i] | i in 1..k])
	% /\
	% objective = load_cost
;

constraint  %% flow out from each processor
	    forall (i in 1..k) (flow_from_processor[i] = sum(j in 1..no_flows, n in k+1..no_links+k where arc[n,1] = i) (flows[j,n]))
;

% constraints on flow_processors; to be the same if they are the same as source or sink
constraint
	forall ( i in 1..no_flows) ( 
	       forall (j in i+1..no_flows where source_destination_actor[i,1] = source_destination_actor[j,1]) (flow_processor[i] = flow_processor[j]))
	/\
	forall ( i in 1..no_flows) ( 
	       forall (j in 1..no_flows where source_destination_actor[i,1] = source_destination_actor[j,2]) (flow_processor[i] = flow_processor[no_flows+j]))
	/\
	forall ( i in 1..no_flows) ( 
	       forall (j in i+1..no_flows where source_destination_actor[i,2] = source_destination_actor[j,2]) (flow_processor[no_flows+i] = flow_processor[no_flows+j]))
;

solve :: seq_search([
            int_search(flow_processor, first_fail, indomain_min, complete),
      	    int_search(total_flow, smallest, indomain_min, complete),
      	    int_search(cost ++ [communication_cost], input_order, indomain_min, complete)
          , int_search( cpu_loads, first_fail, indomain_min, complete)
          , int_search( [inFlow[i,j] | i in 1..no_flows, j in 1..k], first_fail, indomain_min, complete)
          , int_search( [outFlow[i,j] | i in 1..no_flows, j in 1..k], first_fail, indomain_min, complete)
          , int_search( [commFlow[i,j] | i in 1..no_flows, j in 1..no_links], first_fail, indomain_min, complete)
          , int_search( [flows[i,j] | i in 1..no_flows, j in 1..m], first_fail, indomain_min, complete)
          , int_search( actor_processor, first_fail, indomain_min, complete)

      ]) 
      minimize objective;

array[1..no_links] of string: link_str;

% output
% ["Objective = " ++ show(objective) ++ ", Communication_cost = " ++  show(communication_cost) ++ "\n" ++ "Processor loads = " ++ show(cpu_loads) ++"\n"] ++

% ["cpu for actor "++ show(i)++" = " ++ show(actor_processor[i]) ++", " | i in 1..no_actors] ++ ["\n"] ++

% [if i = 1 then "Flow " ++ show(j) ++ " with cost " ++ show(cost[j]) ++ " from processor "++ show(actor_processor[source_destination_actor[j,1]]) ++ " to " ++ show(actor_processor[source_destination_actor[j,2]]) ++ " :\n" ++ 
% if fix(cost[j]) != 0 then 
% if fix(flows[j,i+k]) != 0 then link_str[i] ++ show(flows[j,i+k]) ++ "\n" else "" endif else "" endif
% else
% if fix(flows[j,i+k]) != 0 then link_str[i] ++ show(flows[j,i+k]) ++ "\n" else "" endif endif | j in 1..no_flows, i in 1..no_links] 
% ;
%
output [ 
    "objective = \(objective);\n",
    "communication_cost = \(communication_cost);\n",
    "flow_processor = \(flow_processor);\n",
    "total_flow = \(total_flow);\n",
    "cpu_loads = \(cpu_loads);\n",
    "inFlow = array2d(1..\(no_flows), 1..\(k), \(inFlow));\n",
    "outFlow = array2d(1..\(no_flows), 1..\(k), \(outFlow));\n",
    "commFlow = array2d(1..\(no_flows), 1..\(k), \(commFlow));\n",
    "flows = array2d(1..\(no_flows), 1..\(k), \(flows));\n",
    "actor_processor = \(actor_processor);\n"
];

%% ========= DATA =============
% H263 encoder
%
% Actors
% 1 = mc
% 2 = me
% 3 = vlc
% 4 = mbe
% 5 = mbd

% 1. motion_compensation -> motion_estimation: mc2me 457
% 2. motion_estimation -> mb_encoding: me2mbe 5
% 3. mb_encoding -> vlc: mbe2vlc 457
% 4. mb_encoding -> mb_decoding: mbe2mbd 457
% 5. mb_decoding -> motion_compensation: mbd2mc 457
% 6. vlc -> vlc: vlc2vlc 13
% 7. motion_compensation -> motion_compensation: mc2mc 457

% Load (limit 200)
% motion_compensation 2, motion_estimation 58,
% mb_encoding 125, vlc 4,
% mb_decoding 94,

% Architecture:
%
% ___    ___ 
% |1 |---|2 |
% ---\  /--- 
%  |   X  |  
% ___/  \___ 
% |3 |---|4 |
% ---    --- 

row = 2;
col = 2;

no_links = 2*2*(row-1)*col + 2*2;

no_actors=5;

no_flows = 7;
link_bandwidth = 250;

source_destination_actor = 
			[| 1, 2 |
			   2, 4 |
			   4, 3 |
			   4, 5 |
			   5, 1 |
			   3, 3 |
			   1, 1
			|];

actor_processor = [flow_processor[1], flow_processor[8], flow_processor[6], flow_processor[13], flow_processor[5]];


inStream = [457, 5, 457, 457, 457, 13, 457];

b = [| 0, 0, 0, 0, inStream[1], -inStream[1] |
       0, 0, 0, 0, inStream[2], -inStream[2] |
       0, 0, 0, 0, inStream[3], -inStream[3] |
       0, 0, 0, 0, inStream[4], -inStream[4] |
       0, 0, 0, 0, inStream[5], -inStream[5] |
       0, 0, 0, 0, inStream[6], -inStream[6] |
       0, 0, 0, 0, inStream[7], -inStream[7] |];

flows = array2d(1..no_flows, 1..m, 
        [inFlow[1,i] | i in 1..k] ++ [commFlow[1,i] | i in 1..no_links] ++ [outFlow[1,i] | i in 1..k] ++
        [inFlow[2,i] | i in 1..k] ++ [commFlow[2,i] | i in 1..no_links] ++ [outFlow[2,i] | i in 1..k] ++
	[inFlow[3,i] | i in 1..k] ++ [commFlow[3,i] | i in 1..no_links] ++ [outFlow[3,i] | i in 1..k] ++
	[inFlow[4,i] | i in 1..k] ++ [commFlow[4,i] | i in 1..no_links] ++ [outFlow[4,i] | i in 1..k] ++
	[inFlow[5,i] | i in 1..k] ++ [commFlow[5,i] | i in 1..no_links] ++ [outFlow[5,i] | i in 1..k] ++
	[inFlow[6,i] | i in 1..k] ++ [commFlow[6,i] | i in 1..no_links] ++ [outFlow[6,i] | i in 1..k] ++
	[inFlow[7,i] | i in 1..k] ++ [commFlow[7,i] | i in 1..no_links] ++ [outFlow[7,i] | i in 1..k] );

balance = array2d(1..no_flows, 1..n, [b[i,j] | i in 1..no_flows, j in 1..n]);

unit_cost = [ 0, 0, 0, 0] ++
	    [1 | i in 1..no_links] ++
	    [0, 0, 0, 0];

processor_load = 200;

% mc, me, vlc, mbe, mbd
actor_load = [2, 58, 4, 125, 94];

load = array2d(1..2, 1..no_flows, 
	[if (not exists (k in 1..i-1) (source_destination_actor[k,j+1] = source_destination_actor[i,j+1] \/ 
	    	 	      	       source_destination_actor[k,((j+1) mod 2) + 1] = source_destination_actor[i,j+1])) 
	    then actor_load[source_destination_actor[i,j+1]] else 0 endif | j in 0..1, i in 1..no_flows]);

arc =[| 
    	%% from action to processors
    	5, 1 |
    	5, 2 |
	5, 3 |
	5, 4 |

	1, 2 |
	1, 3 |
	1, 4 |

	2, 1 |
	2, 3 |
	2, 4 |

	3, 1 |
	3, 2 |
	3, 4 |

	4, 1 |
	4, 2 |
	4, 3 |
	
	%% from processors to action
	1, 6 |
    	2, 6 |
	3, 6 |
	4, 6 
	|];

in_connections = [if ((i mod 2) mod 2) = 0 then (k+1)+(i div (2*k)) else ((i div 2) mod k + 1) endif | i in 0..2*no_flows*k-1];
out_connections = [if ((i mod 2) mod 2) = 0 then ((i div 2) mod k + 1) else (k+no_flows+1)+(i div (2*k)) endif | i in 0..2*no_flows*k-1];

all_connections = array2d(1..2*no_flows*k+no_links, 1..2, in_connections ++ [arc[i,j] | i in k+1..no_links+k, j in 1..2] ++ out_connections);

total_flow = [flows[i,j] | i in 1..no_flows, j in 1..k] ++ 
	     comm_full ++ 
             [flows[i,j] | i in 1..no_flows, j in k+no_links+1..2*k+no_links];

total_unit_cost = [0 | i in 1..no_flows, j in 1..k] ++ [ 1 | i in 1..no_links] ++ [0 | i in 1..no_flows, j in 1..k];

total_balance = [0 | i in 1..k] ++ [balance[i,j] | i in 1..no_flows, j in k+1..k+1] ++ [balance[i,j] | i in 1..no_flows, j in k+2..k+2];

link_str = ["1 -> 2 = ", "1 -> 3 = ", "1 -> 4 = ", "2 -> 1 = ", "2 -> 3 = ", "2 -> 4 = ", "3 -> 1 = ", "3 -> 2 = ", "3 -> 4 = ", "4 -> 1 = ", "4 -> 2 = ", "4 -> 3 = "];
