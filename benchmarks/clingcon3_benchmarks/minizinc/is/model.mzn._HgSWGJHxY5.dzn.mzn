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


domSetOfBlockInFunction = array1d(allBlocksInFunction, [{0},{1,12,0},{2,11,0},{3,14,1,12,0},{4,13,1,12,0},{5,0},{6,16,4,13,1,12,0},{7,4,13,1,12,0},{8,17,2,11,0},{9,20,8,17,2,11,0},{10,8,17,2,11,0},{11,0},{12,0},{13,1,12,0},{14,1,12,0},{15,4,13,1,12,0},{16,4,13,1,12,0},{17,2,11,0},{18,2,11,0},{19,8,17,2,11,0},{20,8,17,2,11,0}]);

execFrequencyOfBlockInFunction = array1d(allBlocksInFunction, [16384,6144,10240,3840,2304,16384,1152,2304,6400,2400,6400,16384,16384,6144,6144,2304,2304,10240,10240,6400,6400]);

defEdgesForBlockInFunction = array1d(allBlocksInFunction, [{},{},{49},{34},{44},{20},{45},{13,46},{50},{54},{19,55},{},{},{},{},{},{},{},{},{},{}]);

entryBlockOfFunction = 0;

funLocDomain = [|1, 1, 33, |0, 1, 33, |];

numBlocksInFunction = 21;

numDataInFunction = 59;

numOperationsInFunction = 71;

statesInFunction = [];

inBlock = [|18, 0, |19, 0, |20, 0, |21, 0, |22, 0, |23, 0, |24, 0, |25, 0, |26, 0, |88, 3, |89, 6, |90, 7, |91, 9, |92, 10, |93, 11, |94, 12, |95, 13, |96, 14, |97, 15, |98, 16, |99, 17, |100, 18, |101, 19, |102, 20, |103, 5, |];

inBlockSucc = [|3, 3, 5, |4, 6, 7, |5, 7, 5, |6, 9, 10, |7, 10, 5, |8, 11, 2, |9, 12, 1, |10, 13, 4, |11, 14, 3, |12, 15, 7, |13, 16, 6, |14, 17, 8, |15, 18, 5, |16, 19, 10, |17, 20, 9, |65, 1, 13, |66, 0, 11, |67, 2, 17, |68, 8, 19, |69, 0, 12, |70, 2, 18, |71, 8, 20, |72, 1, 14, |73, 2, 17, |74, 0, 11, |75, 8, 19, |78, 0, 11, |79, 1, 13, |80, 4, 15, |81, 2, 17, |82, 8, 19, |83, 0, 12, |84, 1, 14, |85, 4, 16, |86, 2, 18, |87, 8, 20, |];

locDomain = [|53, 28, 0, 31, |53, 23, 0, 31, |53, 4, 1, 31, |54, 38, 0, 31, |54, 36, 0, 31, |54, 7, 1, 31, |55, 25, 0, 31, |55, 21, 0, 31, |55, 16, 1, 31, |56, 28, 0, 31, |56, 23, 0, 31, |56, 4, 1, 31, |57, 38, 0, 31, |57, 36, 0, 31, |57, 7, 1, 31, |58, 25, 0, 31, |58, 21, 0, 31, |58, 16, 1, 31, |59, 43, 0, 31, |59, 39, 0, 31, |59, 11, 1, 31, |60, 43, 0, 31, |60, 39, 0, 31, |60, 11, 1, 31, |61, 24, 0, 31, |61, 30, 0, 31, |61, 2, 1, 31, |62, 26, 0, 31, |62, 47, 0, 31, |62, 15, 1, 31, |63, 51, 0, 31, |63, 52, 0, 31, |63, 17, 1, 31, |64, 40, 0, 31, |64, 41, 0, 31, |64, 9, 1, 31, |65, 3, locValueForNull, locValueForNull, |66, 2, locValueForNull, locValueForNull, |67, 15, locValueForNull, locValueForNull, |68, 17, locValueForNull, locValueForNull, |69, 2, locValueForNull, locValueForNull, |70, 15, locValueForNull, locValueForNull, |71, 17, locValueForNull, locValueForNull, |72, 3, locValueForNull, locValueForNull, |73, 15, locValueForNull, locValueForNull, |74, 2, locValueForNull, locValueForNull, |75, 17, locValueForNull, locValueForNull, |76, 22, 0, 31, |76, 5, 1, 31, |77, 27, 0, 31, |77, 6, 1, 31, |103, 56, 31, 31, |104, 0, 32, 32, |104, 21, 1, 31, |105, 0, 32, 32, |105, 22, 1, 31, |106, 0, 32, 32, |106, 23, 1, 31, |107, 0, 32, 32, |107, 24, 1, 31, |108, 1, 32, 32, |108, 25, 1, 31, |109, 1, 32, 32, |109, 26, 1, 31, |110, 1, 32, 32, |110, 27, 1, 31, |111, 1, 32, 32, |111, 28, 1, 31, |112, 1, 32, 32, |112, 29, 1, 31, |113, 4, 32, 32, |113, 34, 1, 31, |114, 5, 32, 32, |114, 36, 1, 31, |115, 6, 32, 32, |115, 38, 1, 31, |116, 7, 32, 32, |116, 39, 1, 31, |117, 7, 32, 32, |117, 40, 1, 31, |118, 11, 32, 32, |118, 44, 1, 31, |119, 13, 32, 32, |119, 46, 1, 31, |120, 16, 32, 32, |120, 49, 1, 31, |121, 16, 32, 32, |121, 50, 1, 31, |122, 16, 32, 32, |122, 51, 1, 31, |123, 19, 32, 32, |123, 55, 1, 31, |124, 20, 32, 32, |124, 56, 1, 31, |125, 0, 33, 33, |125, 21, 1, 31, |126, 0, 33, 33, |126, 22, 1, 31, |127, 0, 33, 33, |127, 23, 1, 31, |128, 0, 33, 33, |128, 24, 1, 31, |129, 1, 33, 33, |129, 25, 1, 31, |130, 1, 33, 33, |130, 26, 1, 31, |131, 1, 33, 33, |131, 27, 1, 31, |132, 1, 33, 33, |132, 28, 1, 31, |133, 1, 33, 33, |133, 29, 1, 31, |134, 4, 33, 33, |134, 34, 1, 31, |135, 5, 33, 33, |135, 36, 1, 31, |136, 6, 33, 33, |136, 38, 1, 31, |137, 7, 33, 33, |137, 39, 1, 31, |138, 7, 33, 33, |138, 40, 1, 31, |139, 11, 33, 33, |139, 44, 1, 31, |140, 13, 33, 33, |140, 46, 1, 31, |141, 16, 33, 33, |141, 49, 1, 31, |142, 16, 33, 33, |142, 50, 1, 31, |143, 16, 33, 33, |143, 51, 1, 31, |144, 19, 33, 33, |144, 55, 1, 31, |145, 20, 33, 33, |145, 56, 1, 31, |146, 0, 0, 31, |146, 21, 1, 31, |147, 0, 0, 31, |147, 22, 1, 31, |148, 0, 0, 31, |148, 23, 1, 31, |149, 0, 0, 31, |149, 24, 1, 31, |150, 1, 0, 31, |150, 25, 1, 31, |151, 1, 0, 31, |151, 26, 1, 31, |152, 1, 0, 31, |152, 27, 1, 31, |153, 1, 0, 31, |153, 28, 1, 31, |154, 1, 0, 31, |154, 29, 1, 31, |155, 4, 0, 31, |155, 34, 1, 31, |156, 5, 0, 31, |156, 36, 1, 31, |157, 6, 0, 31, |157, 38, 1, 31, |158, 7, 0, 31, |158, 39, 1, 31, |159, 7, 0, 31, |159, 40, 1, 31, |160, 11, 0, 31, |160, 44, 1, 31, |161, 13, 0, 31, |161, 46, 1, 31, |162, 16, 0, 31, |162, 49, 1, 31, |163, 16, 0, 31, |163, 50, 1, 31, |164, 16, 0, 31, |164, 51, 1, 31, |165, 19, 0, 31, |165, 55, 1, 31, |166, 20, 0, 31, |166, 56, 1, 31, |167, 30, 0, 0, |168, 52, 0, 0, |169, 30, 1, 31, |170, 32, 1, 31, |171, 35, 1, 31, |172, 37, 1, 31, |173, 43, 1, 31, |174, 47, 1, 31, |175, 52, 1, 31, |176, 30, 1, 31, |177, 32, 1, 31, |178, 35, 1, 31, |179, 37, 1, 31, |180, 41, 1, 31, |181, 43, 1, 31, |182, 45, 1, 31, |183, 47, 1, 31, |184, 52, 1, 31, |185, 54, 1, 31, |186, 45, 1, 31, |187, 24, 0, 31, |187, 2, 1, 31, |188, 26, 0, 31, |188, 15, 1, 31, |189, 51, 0, 31, |189, 17, 1, 31, |];

applyDefDomUseConstraintForMatch = array1d(allMatches, [false,false,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]);

codeSizeOfMatch = array1d(allMatches, [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,0,0,4,4,4,4,4,4,4,8,8,8,8,8,8,8,8,8,8,4,4,4,4]);

consumedBlocksInMatch = array1d(allMatches, [{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{}]);

dataDefinedByMatch = array1d(allMatches, [{13},{19},{20},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{58},{57},{0},{1},{8},{10},{12},{14},{18},{31},{33},{42},{48},{53},{21},{22},{23},{24},{25},{26},{27},{28},{29},{34},{36},{38},{39},{40},{44},{46},{49},{50},{51},{55},{56},{4},{7},{16},{4},{7},{16},{11},{11},{2},{15},{17},{9},{3,33},{2,31},{15,48},{17,53},{2,31},{15,48},{17,53},{3,33},{15,47,48},{2,30,31},{17,52,53},{5,35},{6,37},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{21},{22},{23},{24},{25},{26},{27},{28},{29},{34},{36},{38},{39},{40},{44},{46},{49},{50},{51},{55},{56},{21},{22},{23},{24},{25},{26},{27},{28},{29},{34},{36},{38},{39},{40},{44},{46},{49},{50},{51},{55},{56},{21},{22},{23},{24},{25},{26},{27},{28},{29},{34},{36},{38},{39},{40},{44},{46},{49},{50},{51},{55},{56},{30},{52},{30},{32},{35},{37},{43},{47},{52},{30},{32},{35},{37},{41},{43},{45},{47},{52},{54},{45},{2,30},{15,47},{17,52}]);

dataUsedByMatch = array1d(allMatches, [{45,44},{54,50},{34,46},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{2},{3},{9},{15},{17},{0},{0},{0},{0},{1},{1},{1},{1},{1},{4},{5},{6},{7},{7},{11},{13},{16},{16},{16},{19},{20},{28,23},{38,36},{25,21},{28,23},{38,36},{25,21},{43,39},{43,39},{24,30},{26,47},{51,52},{40,41},{29,32,3,33},{24,30,2,31},{26,47,15,48},{51,52,17,53},{24,30,2,31},{26,47,15,48},{51,52,17,53},{29,32,3,33},{26,14,15,47,48},{24,57,2,30,31},{51,57,17,52,53},{22,58,35},{27,58,37},{31},{33},{42},{48},{53},{31},{33},{42},{48},{53},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{56},{0},{0},{0},{0},{1},{1},{1},{1},{1},{4},{5},{6},{7},{7},{11},{13},{16},{16},{16},{19},{20},{0},{0},{0},{0},{1},{1},{1},{1},{1},{4},{5},{6},{7},{7},{11},{13},{16},{16},{16},{19},{20},{0},{0},{0},{0},{1},{1},{1},{1},{1},{4},{5},{6},{7},{7},{11},{13},{16},{16},{16},{19},{20},{57},{57},{57},{58},{58},{58},{10},{14},{57},{57},{58},{58},{58},{8},{10},{12},{14},{57},{18},{12},{24,57,30},{26,14,47},{51,57,52}]);

entryBlockOfMatch = array1d(allMatches, [{},{},{},{3},{6},{7},{9},{10},{11},{12},{13},{14},{15},{16},{17},{18},{19},{20},{0},{0},{0},{0},{0},{0},{0},{0},{0},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{1},{0},{2},{8},{0},{2},{8},{1},{2},{0},{8},{},{},{0},{1},{4},{2},{8},{0},{1},{4},{2},{8},{3},{6},{7},{9},{10},{11},{12},{13},{14},{15},{16},{17},{18},{19},{20},{5},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{}]);

latencyOfMatch = array1d(allMatches, [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,0,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,1,0,0,0]);

nonCopyMatches = {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,187,188,189};

operationsCoveredByMatch = array1d(allMatches, [{8},{12},{13},{16},{18},{19},{22},{23},{61},{62},{63},{64},{65},{66},{67},{68},{69},{70},{},{},{},{},{},{},{},{},{},{35},{37},{46},{52},{57},{25},{26},{27},{28},{29},{30},{31},{32},{33},{38},{40},{42},{43},{44},{48},{50},{53},{54},{55},{59},{60},{2},{5},{10},{2},{5},{10},{7},{7},{0},{9},{11},{6},{15,1,37},{14,0,35},{20,9,52},{21,11,57},{14,0,35},{20,9,52},{21,11,57},{15,1,37},{20,9,51,52},{14,0,34,35},{21,11,56,57},{3,39},{4,41},{14},{15},{17},{20},{21},{14},{15},{17},{20},{21},{16},{18},{19},{22},{23},{61},{62},{63},{64},{65},{66},{67},{68},{69},{70},{24},{25},{26},{27},{28},{29},{30},{31},{32},{33},{38},{40},{42},{43},{44},{48},{50},{53},{54},{55},{59},{60},{25},{26},{27},{28},{29},{30},{31},{32},{33},{38},{40},{42},{43},{44},{48},{50},{53},{54},{55},{59},{60},{25},{26},{27},{28},{29},{30},{31},{32},{33},{38},{40},{42},{43},{44},{48},{50},{53},{54},{55},{59},{60},{34},{56},{34},{36},{39},{41},{47},{51},{56},{34},{36},{39},{41},{45},{47},{49},{51},{56},{58},{49},{0,34},{9,51},{11,56}]);

spannedBlocksInMatch = array1d(allMatches, [{},{},{},{3,5},{6,7},{7,5},{9,10},{10,5},{11,2},{12,1},{13,4},{14,3},{15,7},{16,6},{17,8},{18,5},{19,10},{20,9},{0},{0},{0},{0},{0},{0},{0},{0},{0},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{1,14,13},{0,12,11},{2,18,17},{8,20,19},{0,12,11},{2,18,17},{8,20,19},{1,14,13},{2,18,17},{0,12,11},{8,20,19},{},{},{0,12,11},{1,14,13},{4,16,15},{2,18,17},{8,20,19},{0,12,11},{1,14,13},{4,16,15},{2,18,17},{8,20,19},{3,5},{6,7},{7,5},{9,10},{10,5},{11,2},{12,1},{13,4},{14,3},{15,7},{16,6},{17,8},{18,5},{19,10},{20,9},{5},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{}]);

numLocations = 34;

numMatches = 190;

sameLoc = [|0, 45, 44, |0, 44, 13, |1, 54, 50, |1, 50, 19, |2, 34, 46, |2, 46, 20, |27, 2, 31, |28, 3, 33, |29, 9, 42, |30, 15, 48, |31, 17, 53, |32, 0, 21, |33, 0, 22, |34, 0, 23, |35, 0, 24, |36, 1, 25, |37, 1, 26, |38, 1, 27, |39, 1, 28, |40, 1, 29, |41, 4, 34, |42, 5, 36, |43, 6, 38, |44, 7, 39, |45, 7, 40, |46, 11, 44, |47, 13, 46, |48, 16, 49, |49, 16, 50, |50, 16, 51, |51, 19, 55, |52, 20, 56, |];

