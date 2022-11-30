% Copyright (c) 2013-2015, Gabriel Hjort Blindell <ghb@kth.se>
% All rights reserved.
%
% Redistribution and use in source and binary forms, with or without
% modification, are permitted provided that the following conditions are met:
%
% 1. Redistributions of source code must retain the above copyright notice,
%    this list of conditions and the following disclaimer.
% 2. Redistributions in binary form must reproduce the above copyright notice,
%    this list of conditions and the following disclaimer in the documentation
%    and/or other materials provided with the distribution.
%
% THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
% AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
% IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
% ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
% LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
% CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
% SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
% INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
% CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
% ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
% POSSIBILITY OF SUCH DAMAGE.



%=====================
% EXTERNAL PARAMETERS
%=====================

% Function data.
int: numOperationsInFunction;
int: numDataInFunction;
int: numBlocksInFunction;
int: entryBlockOfFunction;
array[allBlocksInFunction] of set of int: domSetOfBlockInFunction;
array[allBlocksInFunction] of set of int: defEdgesForBlockInFunction;
array[int] of allDataInFunction: statesInFunction;
array[allBlocksInFunction] of int: execFrequencyOfBlockInFunction;

% Target machine data.
int: numLocations;

% Match data.
int: numMatches;
array[allMatches] of set of int: operationsCoveredByMatch;
array[allMatches] of set of int: dataDefinedByMatch;
array[allMatches] of set of int: dataUsedByMatch;
array[allMatches] of set of int: entryBlockOfMatch;
array[allMatches] of set of int: spannedBlocksInMatch;
array[allMatches] of set of int: consumedBlocksInMatch;
array[allMatches] of int: codeSizeOfMatch;
array[allMatches] of int: latencyOfMatch;
array[allMatches] of bool: applyDefDomUseConstraintForMatch;
set of allMatches: nonCopyMatches;

% Arrays that encode constraints
array[int,int] of int: sameLoc;
array[int,int] of int: inBlockSucc;
array[int,int] of int: inBlock;
array[int,int] of int: locDomain;
array[int,int] of int: funLocDomain;

set of allMatches: Dominated;

%=====================
% INTERNAL PARAMETERS
%=====================

% Total number of location values (an additional value will be needed for
% representing the null location, for when the datum cannot be reused by other
% matches).
int: numLocValues = numLocations + 1;

% Total number of blocks values (an additional value will be needed for
% representing the null block, to which non-selected matches will be placed).
int: numBlockValues = numBlocksInFunction + 1;

% Reference to the null-block value.
int: blockValueForNull = numBlockValues - 1;

% Reference to to the null-location value.
int: locValueForNull = numLocValues - 1;

% Extends the external parameter 'domSetOfBlockInFunction' with a value
% for the null block (which is assumed to be dominated by all blocks).
array[allBlocksInFunctionPlusNull] of set of int:
  domSetOfBlockInFunctionPlusNull =
    array1d( allBlocksInFunctionPlusNull
           , domSetOfBlockInFunction
             ++
             array1d( blockValueForNull..blockValueForNull,
                      [allBlocksInFunction]
                    )
           );

% Extends the external parameter 'execFrequencyOfBlockInFunction' with a value
% of 0 for the null block.
array[allBlocksInFunctionPlusNull] of int: execFrequencyOfBlocksPlusNull =
  array1d( allBlocksInFunctionPlusNull
         , execFrequencyOfBlockInFunction
           ++
           array1d(blockValueForNull..blockValueForNull, [0])
         );

% Sets to be used as array ranges.
set of int: allOperationsInFunction = 0..numOperationsInFunction-1;
set of int: allDataInFunction = 0..numDataInFunction-1;
set of int: allBlocksInFunction = 0..numBlocksInFunction-1;
set of int: allBlocksInFunctionPlusNull = 0..numBlockValues-1;
set of int: allMatches = 0..numMatches-1;
set of int: allLocValues = 0..numLocValues-1;



%===========
% VARIABLES
%===========

% Data definitions and locations.
array[allDataInFunction] of var allBlocksInFunction: def;
array[allDataInFunction] of var allLocValues: loc;

% Match selection.
array[allMatches] of var bool: sel;

% Blocks wherein the matches are placed.
array[allMatches] of var allBlocksInFunctionPlusNull: place;

% Block ordering (succ[b] is the block appearing immeditely after block b in the
% generated code).
array[allBlocksInFunctionPlusNull] of var allBlocksInFunctionPlusNull: succ;

% Cost.
var 0..sum (m in allMatches diff Dominated)( latencyOfMatch[m]* max ([execFrequencyOfBlocksPlusNull[x] | x in allBlocksInFunction])): objective;



%====================
% GLOBAL CONSTRAINTS
%====================

include "circuit.mzn";
include "table.mzn";



%============
% CONSTRAINTS
%============

% Enforce that, for each operation, exactly one match must be selected such that
% the operation is covered.
constraint
  forall (o in allOperationsInFunction)
  (
    let {
      set of int: mset = { m | m in allMatches diff Dominated
                                    where o in operationsCoveredByMatch[m]
                         }
    }
    in if card(mset) = 1
       then sel[min(mset)]
       else if card(mset) = 2
            then sel[min(mset)] xor sel[max(mset)]
            else sum (m in mset)
                 (
                   bool2int(sel[m])
                 ) = 1
            endif
       endif
  );

% Enforce that, for each datum, exactly one match must be selected such that
% the datum is defined.
%
% This is an implied constraint, but it also enforces that the patterns for
% defining the function input and constants are selected. Such patterns do not
% cover any operations, they are not entailed in the above constraint for
% exactly covering each operation.
constraint
  forall (e in allDataInFunction)
  (
    let {
      set of int: mset = { m | m in allMatches diff Dominated
                                    where e in dataDefinedByMatch[m]
                         }
    }
    in if card(mset) = 1
       then sel[min(mset)]
       else if card(mset) = 2
            then sel[min(mset)] xor sel[max(mset)]
            else sum (m in mset)
                 (
                   bool2int(sel[m])
                 ) = 1
            endif
       endif
  );

% Implied: The total number of data defined by the selected matches must be
% equal to the number of data in the function graph.
constraint redundant_constraint (
  sum (m in allMatches diff Dominated)
  (
    card(dataDefinedByMatch[m]) * bool2int(sel[m])
  ) = numDataInFunction
);

% Selected matches must not be placed in the null block.
constraint
  forall (m in allMatches)
  (
    sel[m] <-> place[m] != blockValueForNull
  );

% Selected matches that have an entry block must be placed in entry block.
constraint
  forall (m in allMatches diff Dominated)
  (
    % If a match has no entry block, then this set will be empty and hence there
    % will be no such constraint. It is assumed that there will be at most one
    % entry.
    forall (r in entryBlockOfMatch[m])
    (
      place[m] in {r, blockValueForNull}
    )
  );

% Data defined by a selected match must be defined in either the block wherein
% the match is placed or in one of the blocks spanned by the match.
constraint
  forall (m in allMatches diff Dominated)
  (
    forall (e in dataDefinedByMatch[m])
    (
      if (card(spannedBlocksInMatch[m]) > 0)
      then
        sel[m] -> def[e] in spannedBlocksInMatch[m]
      else
        sel[m] -> def[e] = place[m]
      endif
    )
  );

% No selected matches may be placed in a block which is consumed by some
% selected match.
constraint
  forall (m, mm in allMatches, b in consumedBlocksInMatch[m])
  (
    sel[m] -> place[mm] != b
  );

% For every block wherein a datum is defined, there must exist some selected
% match such that it is either placed in that block or that block is part of
% one of the blocks that appear in the selected match.
%
% I am not certain whether this is a strictly required or just an implied
% constraint...
constraint
  forall (e in allDataInFunction, l in allBlocksInFunction)
  (
    def[e] = l
    ->
    exists (m in allMatches diff Dominated)
    (
      place[m] = l \/ (sel[m] /\ l in spannedBlocksInMatch[m])
    )
  );

% A datum with a definition edge with a block must be defined in the block of
% that block.
constraint
  forall (l in allBlocksInFunction)
  (
    forall (e in defEdgesForBlockInFunction[l])
    (
      def[e] = l
    )
  );

% Enforce that every datum is defined in a block such that the block dominates
% all blocks wherein the datum is used. This constraint shall not be applied to
% the generic phi patterns.
%
% The code below is essentially a more efficient implementation of:
%     constraint
%       forall ( m in allMatches, e in dataUsedByMatch[m]
%                     where applyDefDomUseConstraintForMatch[m]
%              )
%       (
%         def[e] in domSetOfBlockInFunctionPlusNull[place[m]]
%       );
int: DomRelSize =
  sum (l in allBlocksInFunction)
  (
    card(domSetOfBlockInFunction[l])
  ) + numBlocksInFunction;
array[1..DomRelSize, 1..2] of allBlocksInFunctionPlusNull: DomRel =
  array2d(1..DomRelSize, 1..2,
    [ if k=1 then i else j endif | i in allBlocksInFunctionPlusNull,
                                   j in domSetOfBlockInFunctionPlusNull[i],
                                   k in 1..2
    ]);

constraint
  forall ( m in allMatches diff Dominated, e in dataUsedByMatch[m]
                where applyDefDomUseConstraintForMatch[m]
         )
  (
    table([place[m], def[e]], DomRel)
  );

% Ensure that succ forms a circuit (thus resulting in an ordering of blocks).
constraint
  circuit(succ) :: domain;

% The block of the entry block (i.e. function entry point) must be placed as the
% first block, and the block of the null block must be placed as the last block.
constraint
  succ[blockValueForNull] = entryBlockOfFunction;

% Constrain the loc value for all data that are states.
constraint
  forall (e in statesInFunction)
  (
    loc[e] = locValueForNull
  );

% Accumulate cost of selected patterns.
% TODO: make this part generic
constraint
  objective = sum (m in allMatches diff Dominated)
         ( latencyOfMatch[m]
         * execFrequencyOfBlocksPlusNull[place[m]]
         );



%===========================
% PARAMETERIZED CONSTRAINTS
%===========================

constraint
  forall(i in index_set_1of2(sameLoc))(
    let {int: m = sameLoc[i,1],
         int: p = sameLoc[i,2],
         int: q = sameLoc[i,3]} in
	sel[m] -> loc[p] = loc[q]
  );

constraint
  forall(i in index_set_1of2(inBlockSucc))(
    let {int: m = inBlockSucc[i,1],
         int: p = inBlockSucc[i,2],
         int: q = inBlockSucc[i,3]} in
	place[m] in {p,blockValueForNull} /\
	(sel[m] -> succ[p] = q)
  );

constraint
  forall(i in index_set_1of2(inBlock))(
    let {int: m = inBlock[i,1],
         int: p = inBlock[i,2]} in
	place[m] in {p,blockValueForNull}
  );

constraint
  forall(i in index_set_1of2(locDomain))(
    let {int: m = locDomain[i,1],
         int: l = locDomain[i,2]} in
	sel[m] -> loc[l] in locDomain[i,3]..locDomain[i,4]
  );

constraint
  forall(i in index_set_1of2(funLocDomain))(
    let {int: l = funLocDomain[i,1]} in
	loc[l] in funLocDomain[i,2]..funLocDomain[i,3]
  );



%======================================
% IMPLIED BY PARAMETERIZED CONSTRAINTS
%======================================

% Two matches can't both be selected, if they imply conflicting successor blocks.
constraint redundant_constraint(
  forall(i in index_set_1of2(inBlockSucc), j in index_set_1of2(inBlockSucc) where i<j)(
    let {int: mi = inBlockSucc[i,1],
         int: pi = inBlockSucc[i,2],
         int: qi = inBlockSucc[i,3],
	 int: mj = inBlockSucc[j,1],
         int: pj = inBlockSucc[j,2],
         int: qj = inBlockSucc[j,3]} in
	(pi=pj xor qi=qj) -> (not sel[mi] \/ not sel[mj])
  )
);

% Two matches can't both be selected, if the first implies that two locations
% are equal, and the second implies that the intersection of their domains is
% empty
constraint redundant_constraint(
  forall(i in index_set_1of2(sameLoc))(
    let {int: m1 = sameLoc[i,1],
         int: p = sameLoc[i,2],
         int: q = sameLoc[i,3]} in
    forall(j1 in index_set_1of2(locDomain) where locDomain[j1,2]=p)(
      forall(j2 in index_set_1of2(locDomain) where locDomain[j2,1]=locDomain[j1,1] /\
                                                   locDomain[j2,2]=q)(
        let {int: m2 = locDomain[j1,1]} in
	    card((locDomain[j1,3]..locDomain[j1,4]) intersect (locDomain[j2,3]..locDomain[j2,4]))=0 ->
            not sel[m1] \/ not sel[m2]
      )
    )
  )
);

% Ad hoc: detect symmetry among location values 1..31
constraint redundant_constraint (
  forall(i in index_set_1of2(funLocDomain))(
    let {int: lo = funLocDomain[i,2],
         int: hi = funLocDomain[i,3]} in
	lo<=31 -> hi>=31 \/ hi=0
  ) /\
  forall(i in index_set_1of2(locDomain))(
    let {int: lo = locDomain[i,3],
         int: hi = locDomain[i,4]} in
	lo<=31 -> hi>=31 \/ hi=0
  ) ->
  forall(i in allDataInFunction)(loc[i] in {0} union (31..numLocValues-1))
);



%===================================================
% DOMINATION DERIVED FROM PARAMETERIZED CONSTRAINTS
%===================================================

% Match m1 dominates match m2 if:
% - neither match occurs in sameLoc, inBlock, inBlockSucc (relax later?)
% - [latencyOfMatch[m1], m1] lex_lt [latencyOfMatch[m2], m2]
% - operationsCoveredByMatch is the same for both matches
% - dataDefinedByMatch   is the same for both matches
% - dataUsedByMatch      is the same for both matches
% - entryBlockOfMatch        is the same for both matches
% - spannedBlocksInMatch    is the same for both matches
% - applyDefDomUseConstraintForMatch    is the same for both matches
% - if m1 defines any side-constraints in locDomain,
%   then m2 defines side-constraints that are at least as strong
test is_dominated(int: m2) =
  let {set of allMatches: exclude = {sameLoc[i,1] | i in index_set_1of2(sameLoc)} % relax later
                              union {inBlock[i,1] | i in index_set_1of2(inBlock)}
			      union {inBlockSucc[i,1] | i in index_set_1of2(inBlockSucc)}} in
  exists(m1 in allMatches where not (m1=m2 \/ m1 in exclude \/ m2 in exclude))(
    ((latencyOfMatch[m1] < latencyOfMatch[m2]) \/
     (latencyOfMatch[m1] = latencyOfMatch[m2] /\ m1 < m2)) /\
    operationsCoveredByMatch[m1] = operationsCoveredByMatch[m2] /\
    dataDefinedByMatch[m1] = dataDefinedByMatch[m2] /\
    dataUsedByMatch[m1] = dataUsedByMatch[m2] /\
    entryBlockOfMatch[m1] = entryBlockOfMatch[m2] /\
    spannedBlocksInMatch[m1] = spannedBlocksInMatch[m2] /\
    applyDefDomUseConstraintForMatch[m1] = applyDefDomUseConstraintForMatch[m2] /\
    forall(i in index_set_1of2(locDomain) where locDomain[i,1] = m1)(
      exists(j in index_set_1of2(locDomain)
             where locDomain[j,1] = m2
                /\ locDomain[j,2] = locDomain[i,2])(
	(locDomain[j,3]..locDomain[j,4]) subset (locDomain[i,3]..locDomain[i,4])
      )
    )
  );

Dominated = {m | m in allMatches where is_dominated(m)};

constraint
  forall(d in Dominated)(not sel[d]);

%==================
% SOLVE AND OUTPUT
%==================

solve ::
  seq_search(
    [ bool_search([ sel[m] | m in nonCopyMatches diff Dominated
                                  where card(operationsCoveredByMatch[m])
                                        +
                                        card(dataDefinedByMatch[m])
                                        > 2
                  ], input_order, indomain_max, complete)
    , bool_search([ sel[m] | m in nonCopyMatches diff Dominated
                                  where card(operationsCoveredByMatch[m])
                                        +
                                        card(dataDefinedByMatch[m])
                                        = 2
				  ], input_order, indomain_max, complete)
    , bool_search([ sel[m] | m in nonCopyMatches diff Dominated
                                  where card(operationsCoveredByMatch[m])
                                        +
                                        card(dataDefinedByMatch[m])
                                        = 1
				  ], input_order, indomain_max, complete)
    , int_search( def, first_fail, indomain_min, complete)
    , int_search( loc, first_fail, indomain_min, complete)
    , int_search( place, first_fail, indomain_min, complete)
    , int_search( succ, first_fail, indomain_min, complete)

	]
  )
minimize objective;

output [ "sel = ", show(sel), ";\n"
       , "def = ", show(def), ";\n"
       , "loc = ", show(loc), ";\n"
       , "place = ", show(place), ";\n"
       , "succ = ", show(succ), ";\n"
       , "blockValueForNull = ", show(blockValueForNull), ";\n"
       , "locValueForNull = ", show(locValueForNull), ";\n"
       , "objective = ", show(objective), ";\n"
       ];


domSetOfBlockInFunction = array1d(allBlocksInFunction, [{0},{1,8,0},{2,7,0},{3,0},{4,9,2,7,0},{5,12,4,9,2,7,0},{6,11,4,9,2,7,0},{7,0},{8,0},{9,2,7,0},{10,2,7,0},{11,4,9,2,7,0},{12,4,9,2,7,0}]);

execFrequencyOfBlockInFunction = array1d(allBlocksInFunction, [16384,8192,8192,16384,4096,1536,2560,16384,16384,8192,8192,4096,4096]);

defEdgesForBlockInFunction = array1d(allBlocksInFunction, [{},{24},{37},{13},{},{34},{36},{},{},{},{},{},{}]);

entryBlockOfFunction = 0;

funLocDomain = [|1, 1, 33, |0, 1, 33, |];

numBlocksInFunction = 13;

numDataInFunction = 41;

numOperationsInFunction = 49;

statesInFunction = [];

inBlock = [|10, 0, |11, 0, |12, 0, |13, 0, |14, 0, |54, 1, |55, 5, |56, 6, |57, 7, |58, 8, |59, 9, |60, 10, |61, 11, |62, 12, |63, 3, |];

inBlockSucc = [|1, 1, 3, |2, 5, 3, |3, 6, 3, |4, 7, 2, |5, 8, 1, |6, 9, 4, |7, 10, 3, |8, 11, 6, |9, 12, 5, |40, 0, 7, |41, 2, 9, |42, 4, 11, |43, 2, 10, |44, 4, 12, |45, 0, 8, |46, 4, 11, |48, 0, 7, |49, 2, 9, |50, 4, 11, |51, 0, 8, |52, 2, 10, |53, 4, 12, |];

locDomain = [|34, 31, 0, 31, |34, 17, 0, 31, |34, 8, 1, 31, |35, 31, 0, 31, |35, 17, 0, 31, |35, 8, 1, 31, |36, 30, 0, 31, |36, 32, 0, 31, |36, 9, 1, 31, |37, 29, 0, 31, |37, 16, 0, 31, |37, 11, 1, 31, |38, 19, 0, 31, |38, 25, 0, 31, |38, 5, 1, 31, |39, 18, 0, 31, |39, 27, 0, 31, |39, 6, 1, 31, |40, 2, locValueForNull, locValueForNull, |41, 5, locValueForNull, locValueForNull, |42, 6, locValueForNull, locValueForNull, |43, 5, locValueForNull, locValueForNull, |44, 6, locValueForNull, locValueForNull, |45, 2, locValueForNull, locValueForNull, |46, 6, locValueForNull, locValueForNull, |47, 15, 0, 31, |47, 3, 1, 31, |63, 38, 31, 31, |64, 1, 32, 32, |64, 16, 1, 31, |65, 1, 32, 32, |65, 17, 1, 31, |66, 1, 32, 32, |66, 18, 1, 31, |67, 1, 32, 32, |67, 19, 1, 31, |68, 1, 32, 32, |68, 20, 1, 31, |69, 7, 32, 32, |69, 29, 1, 31, |70, 7, 32, 32, |70, 30, 1, 31, |71, 8, 32, 32, |71, 32, 1, 31, |72, 9, 32, 32, |72, 33, 1, 31, |73, 11, 32, 32, |73, 35, 1, 31, |74, 1, 33, 33, |74, 16, 1, 31, |75, 1, 33, 33, |75, 17, 1, 31, |76, 1, 33, 33, |76, 18, 1, 31, |77, 1, 33, 33, |77, 19, 1, 31, |78, 1, 33, 33, |78, 20, 1, 31, |79, 7, 33, 33, |79, 29, 1, 31, |80, 7, 33, 33, |80, 30, 1, 31, |81, 8, 33, 33, |81, 32, 1, 31, |82, 9, 33, 33, |82, 33, 1, 31, |83, 11, 33, 33, |83, 35, 1, 31, |84, 1, 0, 31, |84, 16, 1, 31, |85, 1, 0, 31, |85, 17, 1, 31, |86, 1, 0, 31, |86, 18, 1, 31, |87, 1, 0, 31, |87, 19, 1, 31, |88, 1, 0, 31, |88, 20, 1, 31, |89, 7, 0, 31, |89, 29, 1, 31, |90, 7, 0, 31, |90, 30, 1, 31, |91, 8, 0, 31, |91, 32, 1, 31, |92, 9, 0, 31, |92, 33, 1, 31, |93, 11, 0, 31, |93, 35, 1, 31, |94, 37, 0, 0, |95, 27, 0, 0, |96, 31, 0, 0, |97, 23, 1, 31, |98, 37, 1, 31, |99, 21, 1, 31, |100, 25, 1, 31, |101, 27, 1, 31, |102, 31, 1, 31, |103, 23, 1, 31, |104, 37, 1, 31, |105, 21, 1, 31, |106, 25, 1, 31, |107, 27, 1, 31, |108, 31, 1, 31, |109, 14, 0, 31, |109, 7, 1, 31, |110, 33, 0, 31, |110, 10, 1, 31, |111, 35, 0, 31, |111, 12, 1, 31, |112, 19, 0, 31, |112, 5, 1, 31, |113, 18, 0, 31, |113, 6, 1, 31, |];

applyDefDomUseConstraintForMatch = array1d(allMatches, [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]);

codeSizeOfMatch = array1d(allMatches, [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,12,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,0,0,0,4,4,4,4,4,4,8,8,8,8,8,8,0,0,0,4,4]);

consumedBlocksInMatch = array1d(allMatches, [{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{}]);

dataDefinedByMatch = array1d(allMatches, [{13},{},{},{},{},{},{},{},{},{},{40},{39},{0},{1},{4},{22},{26},{28},{14},{15},{24},{34},{36},{38},{16},{17},{18},{19},{20},{29},{30},{32},{33},{35},{8},{8},{9},{11},{5},{6},{2,22},{5,26},{6,28},{5,26},{6,28},{2,22},{6,27,28},{3,23},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{16},{17},{18},{19},{20},{29},{30},{32},{33},{35},{16},{17},{18},{19},{20},{29},{30},{32},{33},{35},{16},{17},{18},{19},{20},{29},{30},{32},{33},{35},{37},{27},{31},{23},{37},{21},{25},{27},{31},{23},{37},{21},{25},{27},{31},{7},{10},{12},{5,25},{6,27}]);

dataUsedByMatch = array1d(allMatches, [{24,34},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{2},{5},{6},{0},{0},{3},{10},{12},{13},{1},{1},{1},{1},{1},{7},{7},{8},{9},{11},{31,17},{31,17},{30,32},{29,16},{19,25},{18,27},{20,21,2,22},{19,25,5,26},{18,27,6,28},{19,25,5,26},{18,27,6,28},{20,21,2,22},{18,40,6,27,28},{15,39,23},{22},{26},{28},{22},{26},{28},{},{},{},{},{},{},{},{},{},{38},{1},{1},{1},{1},{1},{7},{7},{8},{9},{11},{1},{1},{1},{1},{1},{7},{7},{8},{9},{11},{1},{1},{1},{1},{1},{7},{7},{8},{9},{11},{40},{40},{40},{39},{40},{39},{4},{40},{40},{39},{40},{39},{4},{40},{40},{14},{33},{35},{19,4,25},{18,40,27}]);

entryBlockOfMatch = array1d(allMatches, [{},{1},{5},{6},{7},{8},{9},{10},{11},{12},{0},{0},{0},{0},{0},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{0},{2},{4},{2},{4},{0},{4},{},{0},{2},{4},{0},{2},{4},{1},{5},{6},{7},{8},{9},{10},{11},{12},{3},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{}]);

latencyOfMatch = array1d(allMatches, [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,0,0,1,1,1,1,1,1,2,2,2,2,2,2,0,0,0,0,0]);

nonCopyMatches = {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,109,110,111,112,113};

operationsCoveredByMatch = array1d(allMatches, [{10},{12},{15},{16},{43},{44},{45},{46},{47},{48},{},{},{},{},{},{26},{30},{32},{18},{19},{28},{38},{40},{42},{20},{21},{22},{23},{24},{33},{34},{36},{37},{39},{5},{5},{6},{8},{2},{3},{11,0,26},{13,2,30},{14,3,32},{13,2,30},{14,3,32},{11,0,26},{14,3,31,32},{1,27},{11},{13},{14},{11},{13},{14},{12},{15},{16},{43},{44},{45},{46},{47},{48},{17},{20},{21},{22},{23},{24},{33},{34},{36},{37},{39},{20},{21},{22},{23},{24},{33},{34},{36},{37},{39},{20},{21},{22},{23},{24},{33},{34},{36},{37},{39},{41},{31},{35},{27},{41},{25},{29},{31},{35},{27},{41},{25},{29},{31},{35},{4},{7},{9},{2,29},{3,31}]);

spannedBlocksInMatch = array1d(allMatches, [{},{1,3},{5,3},{6,3},{7,2},{8,1},{9,4},{10,3},{11,6},{12,5},{0},{0},{0},{0},{0},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{0,8,7},{2,10,9},{4,12,11},{2,10,9},{4,12,11},{0,8,7},{4,12,11},{},{0,8,7},{2,10,9},{4,12,11},{0,8,7},{2,10,9},{4,12,11},{1,3},{5,3},{6,3},{7,2},{8,1},{9,4},{10,3},{11,6},{12,5},{3},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{}]);

numLocations = 34;

numMatches = 114;

sameLoc = [|0, 24, 34, |0, 34, 13, |15, 2, 22, |16, 5, 26, |17, 6, 28, |18, 0, 14, |19, 0, 15, |20, 3, 24, |21, 10, 34, |22, 12, 36, |23, 13, 38, |24, 1, 16, |25, 1, 17, |26, 1, 18, |27, 1, 19, |28, 1, 20, |29, 7, 29, |30, 7, 30, |31, 8, 32, |32, 9, 33, |33, 11, 35, |];

