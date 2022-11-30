%------------------------------------------------------------------------------%
% gfd-schedule.mzn
%
% Scheduling problem:
%
%   Constraints:
%    * Items are grouped by its 'kind'.
%    * Items are processed by group using 'facility'.
%    * Items must be processed after 'producedDay'.
%    * Maximum number of processed-items/day is fixed.
%
%   Objective:
%     Items may be processed before 'deadLineDay'.
%     Minimize group. (minimize use of facility)
%
%------------------------------------------------------------------------------%
% Includes

include "nvalue.mzn";
include "at_most.mzn";

%------------------------------------------------------------------------------%
% Parameters

% how many items
int: N;

% how many facilities
int: F;

% max items per day
int: MaxItemsPerDay;

% max day of schedule
int: MaxDay;

% item names
array[1..N] of string: name;

% kind of items
array[1..N] of int: kind;

% which facility can be used to process item
array[1..N] of set of 1..F: facility;

% item must be tested after prodecedDay
array[1..N] of int: producedDay;

% item must be tested until deadLineDay
array[1..N] of int: deadLineDay;

%------------------------------------------------------------------------------%
% Variables

% item -> group mapping
array[1..N] of var 1..N: assignedGroup;

% group -> facility mapping (0 if group number not used)
array[1..N] of var 0..F: groupFacility;

array[1..N] of var 0..MaxDay: groupProcessDay;

array[1..N] of var 1..MaxDay: itemProcessDay;

var 1..N: nGroups;

int: dlp_max = sum(i in 1..N)(MaxDay - deadLineDay[i]);
var 0..dlp_max: deadLinePenalty;

int: obj_min = lb(deadLinePenalty) * 100 + lb(nGroups);
int: obj_max = ub(deadLinePenalty) * 100 + ub(nGroups);
var obj_min..obj_max: objective;

%------------------------------------------------------------------------------%
% Constraints

constraint
	forall(i in 1..N) (
		itemProcessDay[i] = groupProcessDay[assignedGroup[i]]
	);

% one group contains only one kind of item
constraint
	forall(i, j in 1..N where i < j) (
		kind[i] != kind[j] -> assignedGroup[i] != assignedGroup[j]
	);

constraint
	forall(k in lb_array(kind)..ub_array(kind)) (
		let {
			int: base = card({ i | i in 1..N where kind[i] < k});
			int: size = card({ i | i in 1..N where kind[i] = k});

			% index set of items having same kind (may be assigned to same group)
			array[1..size] of int: giset = [i |i in 1..N where kind[i] == k];
		} in
		% define group number selection range
		forall(i in index_set(giset)) (
			base < assignedGroup[giset[i]] /\ assignedGroup[giset[i]] <= base + size
		)
	);

% set 0 if not used
constraint
	forall(g in 1..N) (
		exists(i in 1..N)(assignedGroup[i] = g) != true
		<-> (groupFacility[g] == 0 /\ groupProcessDay[g] == 0)
	);

% set group order
constraint symmetry_breaking_constraint(
	forall(k in lb_array(kind)..ub_array(kind)) (
		let {
			int: base = card({ i | i in 1..N where kind[i] < k});
			int: size = card({ i | i in 1..N where kind[i] = k});

			% index set of items having same kind (may be assigned to same group)
			array[1..size] of int: giset = [i |i in 1..N where kind[i] == k];
		} in
		% define group number selection range
		forall(i in index_set(giset)) (
			assignedGroup[giset[i]] <= base + i
		)
		/\
		% use group number from smaller to bigger
		forall(g, h in base+1..base+size where g < h) (
			groupFacility[g] == 0 -> groupFacility[h] = 0
		)
	)
);

% facility is assinged to group according to item's facility
constraint
	forall(i in 1..N) (
		groupFacility[assignedGroup[i]] in facility[i]
	);

% facility must be used by group exclusively
constraint
	forall(i, j in 1..N where i < j) (
	    groupFacility[i] != 0 /\ groupFacility[j] != 0
	    /\ groupFacility[i] == groupFacility[j]
		 -> groupProcessDay[i] != groupProcessDay[j]
	);

% items must be assigned to facility after its producedDay
constraint
	forall(i in 1..N) (
		producedDay[i] < groupProcessDay[assignedGroup[i]]
	);

% items per day
constraint
	forall(d in 1..MaxDay) (
		at_most(MaxItemsPerDay, itemProcessDay, d)
	);

% penalty
function var int: itemDeadLinePenalty(int: i) = (
	if (itemProcessDay[i] <=  deadLineDay[i]) then
	   0
	else
	   itemProcessDay[i] - deadLineDay[i]
	endif
);

constraint
	deadLinePenalty = sum(i in 1..N) (itemDeadLinePenalty(i));

constraint nvalue(nGroups, assignedGroup);


%------------------------------------------------------------------------------%
% Search and solve item

solve 
    :: seq_search([
        int_search(
            assignedGroup ++ groupFacility ++ groupProcessDay,
            first_fail, indomain_min, complete
        ),
        int_search(
            itemProcessDay ++ [nGroups, deadLinePenalty, objective],
            first_fail, indomain_min, complete
        )
    ])
    minimize objective;

%------------------------------------------------------------------------------%
% Output item

output [ 
    "% item\t k, g, f, day\n" 
] ++ [ 
    "% \(name[i])\t \(kind[i]), \(assignedGroup[i]), \(groupFacility[assignedGroup[i]]), \(itemProcessDay[i]) (\(producedDay[i]) - \(deadLineDay[i]))\n"
| i in 1..N 
] ++ [ 
    "assignedGroup = \(assignedGroup);\n", 
	"groupFacility = \(groupFacility);\n",
	"groupProcessDay = \(groupProcessDay);\n",
	"itemProcessDay = \(itemProcessDay);\n",
	"deadLinePenalty = \(deadLinePenalty);\n",
    "nGroups = \(nGroups);\n",
	"objective = \(objective);\n"
];

%------------------------------------------------------------------------------%

N = 120;
F = 5;
MaxItemsPerDay = 50;
MaxDay = 50;
name = ["i1", "i2", "i3", "i4", "i5", "i6", "i7", "i8", "i9", "i10", "i11", "i12", "i13", "i14", "i15", "i16", "i17", "i18", "i19", "i20", "i21", "i22", "i23", "i24", "i25", "i26", "i27", "i28", "i29", "i30", "i31", "i32", "i33", "i34", "i35", "i36", "i37", "i38", "i39", "i40", "i41", "i42", "i43", "i44", "i45", "i46", "i47", "i48", "i49", "i50", "i51", "i52", "i53", "i54", "i55", "i56", "i57", "i58", "i59", "i60", "i61", "i62", "i63", "i64", "i65", "i66", "i67", "i68", "i69", "i70", "i71", "i72", "i73", "i74", "i75", "i76", "i77", "i78", "i79", "i80", "i81", "i82", "i83", "i84", "i85", "i86", "i87", "i88", "i89", "i90", "i91", "i92", "i93", "i94", "i95", "i96", "i97", "i98", "i99", "i100", "i101", "i102", "i103", "i104", "i105", "i106", "i107", "i108", "i109", "i110", "i111", "i112", "i113", "i114", "i115", "i116", "i117", "i118", "i119", "i120"];
kind = [7, 11, 10, 20, 20, 6, 9, 8, 20, 5, 11, 5, 7, 20, 16, 16, 10, 3, 1, 15, 20, 15, 4, 13, 2, 1, 3, 2, 14, 11, 10, 16, 4, 1, 15, 8, 1, 16, 18, 1, 14, 14, 19, 17, 7, 18, 3, 2, 15, 8, 20, 16, 7, 3, 9, 19, 11, 10, 7, 8, 13, 12, 1, 18, 1, 11, 14, 5, 7, 8, 19, 4, 13, 14, 4, 8, 17, 13, 12, 12, 20, 2, 3, 18, 7, 7, 7, 1, 14, 7, 5, 3, 11, 14, 6, 7, 7, 17, 8, 15, 13, 7, 20, 5, 1, 15, 15, 9, 4, 12, 4, 18, 8, 4, 2, 2, 18, 16, 8, 13];
facility = [
  { 2 },
  { 3, 4, 5 },
  { 2, 5 },
  { 4, 5 },
  { 3 },
  { 1 },
  { 2, 3, 5 },
  { 2 },
  { 3 },
  { 1, 2, 5 },
  { 4 },
  { 1, 3, 5 },
  { 1, 2, 5 },
  { 2, 3, 4 },
  { 3, 4 },
  { 2, 4 },
  { 1, 4, 5 },
  { 1, 3, 4, 5 },
  { 1, 2, 3, 5 },
  { 3 },
  { 1, 2, 4, 5 },
  { 2, 5 },
  { 1, 2, 3, 4 },
  { 1, 3, 5 },
  { 1, 2, 3, 4, 5 },
  { 1, 2, 5 },
  { 2, 3 },
  { 1, 2, 4, 5 },
  { 1, 2, 3 },
  { 2, 3, 5 },
  { 3 },
  { 2 },
  { 3, 4, 5 },
  { 1, 4, 5 },
  { 3, 5 },
  { 2, 3, 4, 5 },
  { 1, 3, 4 },
  { 3, 5 },
  { 1, 3, 4 },
  { 1, 3, 4, 5 },
  { 1, 3, 5 },
  { 1, 3 },
  { 2, 3, 4, 5 },
  { 3, 5 },
  { 1, 2, 4 },
  { 1, 3, 4 },
  { 3, 4, 5 },
  { 2, 3, 4 },
  { 2, 3, 4, 5 },
  { 1, 2, 4 },
  { 1 },
  { 1, 2 },
  { 1, 2, 3, 5 },
  { 1, 3, 5 },
  { 1, 3, 5 },
  { 1, 2, 3 },
  { 1, 2, 3 },
  { 1, 5 },
  { 1, 2, 4, 5 },
  { 1, 2, 4 },
  { 1, 5 },
  { 1, 2, 5 },
  { 1 },
  { 2, 5 },
  { 1, 4 },
  { 2, 3, 5 },
  { 2 },
  { 2, 5 },
  { 1, 3, 4 },
  { 1, 5 },
  { 2, 3 },
  { 1, 3, 4, 5 },
  { 1, 2, 4 },
  { 4 },
  { 1, 3, 4, 5 },
  { 1, 3 },
  { 2, 3 },
  { 5 },
  { 1, 3, 5 },
  { 1, 2, 5 },
  { 3 },
  { 2, 3, 5 },
  { 3, 5 },
  { 1, 3, 4 },
  { 2, 3, 4, 5 },
  { 1 },
  { 1, 3 },
  { 1, 4, 5 },
  { 3, 4, 5 },
  { 1, 5 },
  { 1, 2, 4, 5 },
  { 3, 4 },
  { 2 },
  { 3, 5 },
  { 1 },
  { 5 },
  { 2, 3, 4, 5 },
  { 1, 2, 5 },
  { 1, 4, 5 },
  { 1, 2, 4, 5 },
  { 4, 5 },
  { 3, 4 },
  { 1, 2, 3 },
  { 1, 2, 3, 4, 5 },
  { 1, 2 },
  { 1, 3, 5 },
  { 3, 5 },
  { 2, 3, 4, 5 },
  { 1, 2, 4 },
  { 2, 4 },
  { 3, 4 },
  { 1, 3, 5 },
  { 1, 2, 3, 5 },
  { 1, 4, 5 },
  { 1, 2, 3, 5 },
  { 1, 2, 3 },
  { 4 },
  { 1, 3, 4, 5 },
  { 2 },
  { 1 }
];
producedDay = [25, 25, 25, 17, 25, 25, 25, 25, 25, 25, 25, 4, 25, 25, 25, 25, 25, 25, 25, 14, 25, 25, 25, 25, 14, 2, 25, 25, 25, 3, 25, 25, 25, 25, 25, 21, 25, 25, 2, 25, 25, 25, 25, 25, 25, 21, 25, 25, 25, 25, 25, 25, 25, 25, 13, 25, 25, 13, 25, 25, 25, 15, 25, 25, 25, 25, 25, 19, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 5, 25, 25, 25, 25, 25, 25, 1, 25, 24, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 7, 25, 25, 25, 1, 3, 25, 2, 25];
deadLineDay = [27, 40, 50, 40, 50, 28, 42, 27, 50, 50, 50, 13, 50, 50, 37, 50, 50, 50, 50, 50, 50, 38, 50, 50, 35, 37, 50, 50, 50, 36, 42, 48, 50, 27, 34, 50, 30, 50, 27, 28, 50, 50, 50, 41, 50, 39, 38, 49, 50, 48, 50, 26, 49, 30, 50, 28, 48, 40, 47, 48, 50, 50, 27, 35, 50, 50, 40, 50, 50, 45, 43, 49, 33, 50, 50, 50, 50, 39, 50, 43, 50, 32, 40, 48, 50, 50, 50, 50, 50, 42, 43, 50, 50, 50, 40, 50, 10, 50, 50, 49, 50, 47, 44, 50, 41, 32, 50, 50, 36, 50, 27, 40, 50, 43, 33, 21, 34, 47, 44, 50];
