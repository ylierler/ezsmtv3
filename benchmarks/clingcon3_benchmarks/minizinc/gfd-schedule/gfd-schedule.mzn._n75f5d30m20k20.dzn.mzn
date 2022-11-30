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

N = 75;
F = 2;
MaxItemsPerDay = 20;
MaxDay = 30;
name = ["i1", "i2", "i3", "i4", "i5", "i6", "i7", "i8", "i9", "i10", "i11", "i12", "i13", "i14", "i15", "i16", "i17", "i18", "i19", "i20", "i21", "i22", "i23", "i24", "i25", "i26", "i27", "i28", "i29", "i30", "i31", "i32", "i33", "i34", "i35", "i36", "i37", "i38", "i39", "i40", "i41", "i42", "i43", "i44", "i45", "i46", "i47", "i48", "i49", "i50", "i51", "i52", "i53", "i54", "i55", "i56", "i57", "i58", "i59", "i60", "i61", "i62", "i63", "i64", "i65", "i66", "i67", "i68", "i69", "i70", "i71", "i72", "i73", "i74", "i75"];
kind = [7, 12, 11, 20, 16, 12, 3, 5, 7, 1, 12, 2, 7, 1, 19, 19, 7, 16, 10, 13, 17, 14, 15, 18, 12, 15, 19, 5, 11, 12, 17, 15, 3, 1, 15, 13, 14, 20, 6, 9, 7, 18, 1, 11, 7, 6, 1, 15, 17, 1, 11, 7, 2, 13, 9, 15, 6, 13, 16, 9, 7, 20, 2, 15, 15, 8, 9, 12, 20, 12, 10, 7, 9, 19, 2];
facility = [
  { 1 },
  { 2 },
  { 1 },
  { 1, 2 },
  { 1, 2 },
  { 1, 2 },
  { 2 },
  { 1 },
  { 1 },
  { 1 },
  { 2 },
  { 1, 2 },
  { 1, 2 },
  { 1 },
  { 1 },
  { 2 },
  { 2 },
  { 2 },
  { 2 },
  { 2 },
  { 1 },
  { 1 },
  { 1, 2 },
  { 1, 2 },
  { 1, 2 },
  { 1 },
  { 2 },
  { 2 },
  { 1 },
  { 2 },
  { 2 },
  { 1, 2 },
  { 1 },
  { 1, 2 },
  { 1, 2 },
  { 2 },
  { 1 },
  { 2 },
  { 1, 2 },
  { 2 },
  { 1 },
  { 2 },
  { 1, 2 },
  { 2 },
  { 1, 2 },
  { 1, 2 },
  { 1, 2 },
  { 1 },
  { 1, 2 },
  { 1, 2 },
  { 1 },
  { 1 },
  { 2 },
  { 1, 2 },
  { 2 },
  { 2 },
  { 2 },
  { 1 },
  { 1 },
  { 2 },
  { 2 },
  { 2 },
  { 1, 2 },
  { 1, 2 },
  { 1, 2 },
  { 1, 2 },
  { 1 },
  { 2 },
  { 1 },
  { 1 },
  { 1 },
  { 1, 2 },
  { 1 },
  { 1 },
  { 2 }
];
producedDay = [15, 15, 15, 15, 15, 15, 4, 15, 15, 15, 15, 2, 15, 15, 7, 15, 15, 15, 15, 15, 15, 14, 15, 15, 15, 5, 15, 15, 15, 15, 15, 15, 1, 10, 3, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 13, 9, 15, 15, 15, 15, 15, 15, 5, 15, 15, 15, 15, 15, 15, 10, 15, 15, 15, 15, 7, 15, 15, 15, 15, 13, 15, 8, 15, 15];
deadLineDay = [30, 30, 29, 23, 26, 17, 24, 30, 22, 30, 22, 18, 16, 25, 30, 30, 30, 23, 30, 30, 30, 30, 30, 19, 30, 30, 22, 30, 24, 18, 30, 18, 11, 19, 28, 30, 23, 30, 16, 27, 26, 30, 24, 29, 29, 30, 23, 30, 30, 16, 30, 30, 30, 19, 30, 23, 30, 23, 30, 30, 23, 23, 30, 27, 30, 28, 17, 16, 25, 23, 17, 18, 30, 30, 25];
