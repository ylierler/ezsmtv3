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


domSetOfBlockInFunction = array1d(allBlocksInFunction, [{0},{1,0},{2,12,0},{3,15,2,12,0},{4,14,2,12,0},{5,17,4,14,2,12,0},{6,16,4,14,2,12,0},{7,19,5,17,4,14,2,12,0},{8,18,5,17,4,14,2,12,0},{9,20,8,18,5,17,4,14,2,12,0},{10,23,9,20,8,18,5,17,4,14,2,12,0},{11,22,9,20,8,18,5,17,4,14,2,12,0},{12,0},{13,0},{14,2,12,0},{15,2,12,0},{16,4,14,2,12,0},{17,4,14,2,12,0},{18,5,17,4,14,2,12,0},{19,5,17,4,14,2,12,0},{20,8,18,5,17,4,14,2,12,0},{21,8,18,5,17,4,14,2,12,0},{22,9,20,8,18,5,17,4,14,2,12,0},{23,9,20,8,18,5,17,4,14,2,12,0}]);

execFrequencyOfBlockInFunction = array1d(allBlocksInFunction, [16384,16384,8192,4096,4096,1536,2560,768,768,384,240,144,16384,16384,8192,8192,4096,4096,1536,1536,768,768,384,384]);

defEdgesForBlockInFunction = array1d(allBlocksInFunction, [{60},{19},{},{36},{},{},{59},{46},{61},{},{54},{56},{},{},{},{},{},{},{},{},{},{},{},{}]);

entryBlockOfFunction = 0;

funLocDomain = [|1, 1, 33, |0, 1, 33, |];

numBlocksInFunction = 24;

numDataInFunction = 66;

numOperationsInFunction = 85;

statesInFunction = [];

inBlock = [|18, 0, |19, 0, |20, 0, |21, 0, |22, 0, |90, 3, |91, 7, |92, 10, |93, 11, |94, 6, |95, 12, |96, 13, |97, 14, |98, 15, |99, 16, |100, 17, |101, 18, |102, 19, |103, 20, |104, 21, |105, 22, |106, 23, |107, 1, |];

inBlockSucc = [|1, 3, 1, |2, 7, 1, |3, 10, 1, |4, 11, 1, |5, 6, 1, |6, 12, 2, |7, 13, 1, |8, 14, 4, |9, 15, 3, |10, 16, 6, |11, 17, 5, |12, 18, 8, |13, 19, 7, |14, 20, 9, |15, 21, 1, |16, 22, 11, |17, 23, 10, |63, 0, 12, |64, 5, 18, |65, 9, 22, |66, 2, 14, |67, 4, 16, |68, 8, 20, |69, 2, 15, |70, 4, 17, |71, 8, 21, |72, 0, 13, |73, 5, 19, |74, 9, 23, |75, 4, 16, |78, 0, 12, |79, 2, 14, |80, 4, 16, |81, 5, 18, |82, 8, 20, |83, 9, 22, |84, 0, 13, |85, 2, 15, |86, 4, 17, |87, 5, 19, |88, 8, 21, |89, 9, 23, |];

locDomain = [|55, 39, 0, 31, |55, 27, 0, 31, |55, 6, 1, 31, |56, 39, 0, 31, |56, 27, 0, 31, |56, 6, 1, 31, |57, 52, 0, 31, |57, 25, 0, 31, |57, 12, 1, 31, |58, 57, 0, 31, |58, 24, 0, 31, |58, 17, 1, 31, |59, 51, 0, 31, |59, 40, 0, 31, |59, 14, 1, 31, |60, 29, 0, 31, |60, 33, 0, 31, |60, 3, 1, 31, |61, 28, 0, 31, |61, 37, 0, 31, |61, 5, 1, 31, |62, 41, 0, 31, |62, 47, 0, 31, |62, 9, 1, 31, |63, 2, locValueForNull, locValueForNull, |64, 7, locValueForNull, locValueForNull, |65, 10, locValueForNull, locValueForNull, |66, 3, locValueForNull, locValueForNull, |67, 5, locValueForNull, locValueForNull, |68, 9, locValueForNull, locValueForNull, |69, 3, locValueForNull, locValueForNull, |70, 5, locValueForNull, locValueForNull, |71, 9, locValueForNull, locValueForNull, |72, 2, locValueForNull, locValueForNull, |73, 7, locValueForNull, locValueForNull, |74, 10, locValueForNull, locValueForNull, |75, 5, locValueForNull, locValueForNull, |76, 23, 0, 31, |76, 4, 1, 31, |77, 22, 0, 31, |77, 8, 1, 31, |107, 62, 31, 31, |108, 1, 32, 32, |108, 24, 1, 31, |109, 1, 32, 32, |109, 25, 1, 31, |110, 1, 32, 32, |110, 26, 1, 31, |111, 1, 32, 32, |111, 27, 1, 31, |112, 1, 32, 32, |112, 28, 1, 31, |113, 1, 32, 32, |113, 29, 1, 31, |114, 1, 32, 32, |114, 30, 1, 31, |115, 6, 32, 32, |115, 40, 1, 31, |116, 6, 32, 32, |116, 41, 1, 31, |117, 6, 32, 32, |117, 42, 1, 31, |118, 11, 32, 32, |118, 51, 1, 31, |119, 11, 32, 32, |119, 52, 1, 31, |120, 12, 32, 32, |120, 53, 1, 31, |121, 14, 32, 32, |121, 55, 1, 31, |122, 16, 32, 32, |122, 57, 1, 31, |123, 17, 32, 32, |123, 58, 1, 31, |124, 1, 33, 33, |124, 24, 1, 31, |125, 1, 33, 33, |125, 25, 1, 31, |126, 1, 33, 33, |126, 26, 1, 31, |127, 1, 33, 33, |127, 27, 1, 31, |128, 1, 33, 33, |128, 28, 1, 31, |129, 1, 33, 33, |129, 29, 1, 31, |130, 1, 33, 33, |130, 30, 1, 31, |131, 6, 33, 33, |131, 40, 1, 31, |132, 6, 33, 33, |132, 41, 1, 31, |133, 6, 33, 33, |133, 42, 1, 31, |134, 11, 33, 33, |134, 51, 1, 31, |135, 11, 33, 33, |135, 52, 1, 31, |136, 12, 33, 33, |136, 53, 1, 31, |137, 14, 33, 33, |137, 55, 1, 31, |138, 16, 33, 33, |138, 57, 1, 31, |139, 17, 33, 33, |139, 58, 1, 31, |140, 1, 0, 31, |140, 24, 1, 31, |141, 1, 0, 31, |141, 25, 1, 31, |142, 1, 0, 31, |142, 26, 1, 31, |143, 1, 0, 31, |143, 27, 1, 31, |144, 1, 0, 31, |144, 28, 1, 31, |145, 1, 0, 31, |145, 29, 1, 31, |146, 1, 0, 31, |146, 30, 1, 31, |147, 6, 0, 31, |147, 40, 1, 31, |148, 6, 0, 31, |148, 41, 1, 31, |149, 6, 0, 31, |149, 42, 1, 31, |150, 11, 0, 31, |150, 51, 1, 31, |151, 11, 0, 31, |151, 52, 1, 31, |152, 12, 0, 31, |152, 53, 1, 31, |153, 14, 0, 31, |153, 55, 1, 31, |154, 16, 0, 31, |154, 57, 1, 31, |155, 17, 0, 31, |155, 58, 1, 31, |156, 60, 0, 0, |157, 61, 0, 0, |158, 37, 0, 0, |159, 39, 0, 0, |160, 49, 0, 0, |161, 35, 1, 31, |162, 45, 1, 31, |163, 60, 1, 31, |164, 61, 1, 31, |165, 31, 1, 31, |166, 33, 1, 31, |167, 37, 1, 31, |168, 39, 1, 31, |169, 43, 1, 31, |170, 47, 1, 31, |171, 49, 1, 31, |172, 35, 1, 31, |173, 45, 1, 31, |174, 60, 1, 31, |175, 61, 1, 31, |176, 31, 1, 31, |177, 33, 1, 31, |178, 37, 1, 31, |179, 39, 1, 31, |180, 43, 1, 31, |181, 47, 1, 31, |182, 49, 1, 31, |183, 21, 0, 31, |183, 11, 1, 31, |184, 20, 0, 31, |184, 16, 1, 31, |185, 53, 0, 31, |185, 13, 1, 31, |186, 55, 0, 31, |186, 15, 1, 31, |187, 58, 0, 31, |187, 18, 1, 31, |188, 29, 0, 31, |188, 3, 1, 31, |189, 28, 0, 31, |189, 5, 1, 31, |190, 41, 0, 31, |190, 9, 1, 31, |];

applyDefDomUseConstraintForMatch = array1d(allMatches, [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]);

codeSizeOfMatch = array1d(allMatches, [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,12,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,0,0,0,0,0,4,4,4,4,4,4,4,4,4,4,4,8,8,8,8,8,8,8,8,8,8,8,0,0,0,0,0,4,4,4]);

consumedBlocksInMatch = array1d(allMatches, [{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{}]);

dataDefinedByMatch = array1d(allMatches, [{19},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{65},{64},{63},{0},{1},{32},{34},{38},{44},{48},{50},{20},{21},{22},{23},{36},{46},{54},{56},{59},{62},{24},{25},{26},{27},{28},{29},{30},{40},{41},{42},{51},{52},{53},{55},{57},{58},{6},{6},{12},{17},{14},{3},{5},{9},{2,32},{7,44},{10,50},{3,34},{5,38},{9,48},{3,34},{5,38},{9,48},{2,32},{7,44},{10,50},{5,37,38},{4,35},{8,45},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{24},{25},{26},{27},{28},{29},{30},{40},{41},{42},{51},{52},{53},{55},{57},{58},{24},{25},{26},{27},{28},{29},{30},{40},{41},{42},{51},{52},{53},{55},{57},{58},{24},{25},{26},{27},{28},{29},{30},{40},{41},{42},{51},{52},{53},{55},{57},{58},{60},{61},{37},{39},{49},{35},{45},{60},{61},{31},{33},{37},{39},{43},{47},{49},{35},{45},{60},{61},{31},{33},{37},{39},{43},{47},{49},{11},{16},{13},{15},{18},{3,33},{5,37},{9,47}]);

dataUsedByMatch = array1d(allMatches, [{36,59},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{2},{3},{5},{7},{9},{10},{0},{0},{0},{0},{4},{8},{13},{15},{18},{19},{1},{1},{1},{1},{1},{1},{1},{6},{6},{6},{11},{11},{12},{14},{16},{17},{39,27},{39,27},{52,25},{57,24},{51,40},{29,33},{28,37},{41,47},{30,31,2,32},{42,43,7,44},{26,49,10,50},{29,33,3,34},{28,37,5,38},{41,47,9,48},{29,33,3,34},{28,37,5,38},{41,47,9,48},{30,31,2,32},{42,43,7,44},{26,49,10,50},{28,65,5,37,38},{23,63,35},{22,63,45},{32},{34},{38},{44},{48},{50},{32},{34},{38},{44},{48},{50},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{62},{1},{1},{1},{1},{1},{1},{1},{6},{6},{6},{11},{11},{12},{14},{16},{17},{1},{1},{1},{1},{1},{1},{1},{6},{6},{6},{11},{11},{12},{14},{16},{17},{1},{1},{1},{1},{1},{1},{1},{6},{6},{6},{11},{11},{12},{14},{16},{17},{65},{65},{65},{65},{65},{63},{63},{65},{65},{63},{64},{65},{65},{63},{64},{65},{63},{63},{65},{65},{63},{64},{65},{65},{63},{64},{65},{21},{20},{53},{55},{58},{29,64,33},{28,65,37},{41,64,47}]);

entryBlockOfMatch = array1d(allMatches, [{},{3},{7},{10},{11},{6},{12},{13},{14},{15},{16},{17},{18},{19},{20},{21},{22},{23},{0},{0},{0},{0},{0},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{0},{5},{9},{2},{4},{8},{2},{4},{8},{0},{5},{9},{4},{},{},{0},{2},{4},{5},{8},{9},{0},{2},{4},{5},{8},{9},{3},{7},{10},{11},{6},{12},{13},{14},{15},{16},{17},{18},{19},{20},{21},{22},{23},{1},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{}]);

latencyOfMatch = array1d(allMatches, [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,0,0,0,0,0,0,0,0]);

nonCopyMatches = {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,183,184,185,186,187,188,189,190};

operationsCoveredByMatch = array1d(allMatches, [{17},{20},{23},{26},{27},{28},{73},{74},{75},{76},{77},{78},{79},{80},{81},{82},{83},{84},{},{},{},{},{},{42},{44},{48},{54},{58},{60},{30},{31},{32},{33},{46},{56},{64},{66},{69},{72},{34},{35},{36},{37},{38},{39},{40},{50},{51},{52},{61},{62},{63},{65},{67},{68},{4},{4},{10},{15},{12},{1},{3},{7},{18,0,42},{22,5,54},{25,8,60},{19,1,44},{21,3,48},{24,7,58},{19,1,44},{21,3,48},{24,7,58},{18,0,42},{22,5,54},{25,8,60},{21,3,47,48},{2,45},{6,55},{18},{19},{21},{22},{24},{25},{18},{19},{21},{22},{24},{25},{20},{23},{26},{27},{28},{73},{74},{75},{76},{77},{78},{79},{80},{81},{82},{83},{84},{29},{34},{35},{36},{37},{38},{39},{40},{50},{51},{52},{61},{62},{63},{65},{67},{68},{34},{35},{36},{37},{38},{39},{40},{50},{51},{52},{61},{62},{63},{65},{67},{68},{34},{35},{36},{37},{38},{39},{40},{50},{51},{52},{61},{62},{63},{65},{67},{68},{70},{71},{47},{49},{59},{45},{55},{70},{71},{41},{43},{47},{49},{53},{57},{59},{45},{55},{70},{71},{41},{43},{47},{49},{53},{57},{59},{9},{14},{11},{13},{16},{1,43},{3,47},{7,57}]);

spannedBlocksInMatch = array1d(allMatches, [{},{3,1},{7,1},{10,1},{11,1},{6,1},{12,2},{13,1},{14,4},{15,3},{16,6},{17,5},{18,8},{19,7},{20,9},{21,1},{22,11},{23,10},{0},{0},{0},{0},{0},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{0,13,12},{5,19,18},{9,23,22},{2,15,14},{4,17,16},{8,21,20},{2,15,14},{4,17,16},{8,21,20},{0,13,12},{5,19,18},{9,23,22},{4,17,16},{},{},{0,13,12},{2,15,14},{4,17,16},{5,19,18},{8,21,20},{9,23,22},{0,13,12},{2,15,14},{4,17,16},{5,19,18},{8,21,20},{9,23,22},{3,1},{7,1},{10,1},{11,1},{6,1},{12,2},{13,1},{14,4},{15,3},{16,6},{17,5},{18,8},{19,7},{20,9},{21,1},{22,11},{23,10},{1},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{}]);

numLocations = 34;

numMatches = 191;

sameLoc = [|0, 36, 59, |0, 59, 19, |23, 2, 32, |24, 3, 34, |25, 5, 38, |26, 7, 44, |27, 9, 48, |28, 10, 50, |29, 0, 20, |30, 0, 21, |31, 0, 22, |32, 0, 23, |33, 4, 36, |34, 8, 46, |35, 13, 54, |36, 15, 56, |37, 18, 59, |38, 19, 62, |39, 1, 24, |40, 1, 25, |41, 1, 26, |42, 1, 27, |43, 1, 28, |44, 1, 29, |45, 1, 30, |46, 6, 40, |47, 6, 41, |48, 6, 42, |49, 11, 51, |50, 11, 52, |51, 12, 53, |52, 14, 55, |53, 16, 57, |54, 17, 58, |];

