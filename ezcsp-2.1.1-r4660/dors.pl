:- use_module(library(system)).
:- use_module(library(fdbg)).
%:- fdbg_on([no_constraint_hook,labeling_hook(my_fdbg_label_show)]).
%:- fdbg_on([constraint_hook(my_fdbg_show),labeling_hook(my_fdbg_label_show)]).
%:- fdbg_on([no_constraint_hook,no_labeling_hook]).

dors_store_fdvar_names([(ASPName,Var)|Mapping]) :-
	var(Var),
	!,
	fdbg_annotate(Var, fdvar(Name,_,_) , _),
	assert(varmap(Name,ASPName)),
	dors_store_fdvar_names(Mapping).
%
dors_store_fdvar_names([_|Mapping]) :-
	dors_store_fdvar_names(Mapping).
%
dors_store_fdvar_names([]) :-
	assert(choice_stack([])).

get_fdvar_name(Var,Name) :-
	varmap(Var,Name),
	!.
%
get_fdvar_name(Var,Var).  % should never happen


show_stack :-
	!.	% skip the output below
%
show_stack :-
	choice_stack(Stack),
	length(Stack,N),
	write('stack: {'),
	write(N),
	write('} '),
	write(Stack),nl.

dors_output_stack :-
	dors_prolog_stack_save(yes),
	dors_prolog_stack_save(file(F)),
	choice_stack(Stack),
	!,
	reverse(Stack,RevStack),
%	length(RevStack,N),
	( dors_prolog_stack_save_append(yes) ->
		Mode = append ; Mode = write
	),
	open(F,Mode,Stream),
	current_output(OldStream),
	set_output(Stream),
%	write('length: '),write(N),nl,
	writeq(RevStack),write('.'),nl,
	set_output(OldStream),
	close(Stream).

dors_output_stack.
% when dors_prolog_stack_save(no)


dors_check_stack_dump(_,ASPOrderList) :-
	dors_prolog_stack_load(yes),
	dors_prolog_stack_load(file(F)),
	dors_prolog_stack_type(StackType),
	file_exists(F),
	!,
	seeing(OldStream),
	see(F),
	read(RevStack),
	seen,
	see(OldStream),
	revstack_to_asp_order_list(1,StackType,RevStack,ASPOrderList),
	assert(dors_stack(loaded)),
	assert(dors_stack_in(RevStack)),
	assert(dors_stack_type(StackType)),
write('using: '),write(ASPOrderList),nl.
%
dors_check_stack_dump(ASPOrderListFromProgram,ASPOrderListFromProgram) :-
	assert(dors_stack(from_program)),
% when dors_prolog_stack_load(no) or file does not exist
	!.

revstack_to_asp_order_list(N,single,[bisect(Var,_,_)|RevStack],[(N,Var)|ASPOrderList]) :-
	N2 is N + 1,
	revstack_to_asp_order_list(N2,single,RevStack,ASPOrderList).
%
revstack_to_asp_order_list(N,merged,[Level|RevStack],ASPOrderList) :-
	N2 is N + 1,
	revstack_to_asp_order_list_aux(N,Level,LevelVars),
	revstack_to_asp_order_list(N2,merged,RevStack,PartialASPOrderList),
	append(LevelVars,PartialASPOrderList,ASPOrderList).
%
revstack_to_asp_order_list(_,_,[],[]).
%
revstack_to_asp_order_list_aux(N,[(bisect(Var,_,_),_)|Level],[(N,Var)|ASPOrderList]) :-
	revstack_to_asp_order_list_aux(N,Level,ASPOrderList).
%
revstack_to_asp_order_list_aux(N,[(bisect2(Var,_),_)|Level],[(N,Var)|ASPOrderList]) :-
	revstack_to_asp_order_list_aux(N,Level,ASPOrderList).
%
revstack_to_asp_order_list_aux(_,[],[]).

inverse_entry(bisect(Var,=<,Val),bisect(Var,>,Val)).
inverse_entry(bisect(Var,=<,Val),bisect(Var,>=,Val2)) :-
	Val2 is Val + 1.

inverse_entry(bisect(Var,<,Val),bisect(Var,>=,Val)).
inverse_entry(bisect(Var,<,Val),bisect(Var,>,Val2)) :-
	Val2 is Val - 1.

inverse_entry(bisect(Var,>,Val),bisect(Var,=<,Val)).
inverse_entry(bisect(Var,>,Val),bisect(Var,<,Val2)) :-
	Val2 is Val + 1.

inverse_entry(bisect(Var,>=,Val),bisect(Var,<,Val)).
inverse_entry(bisect(Var,>=,Val),bisect(Var,=<,Val2)) :-
	Val2 is Val - 1.

to_stack0(Name,'$labeling_step'(X,Rel,Val,bisect)) :-
	to_stack(Name,'$labeling_step'(X,Rel,Val,bisect)).

to_stack0(Name,forced(X,Rel,Val)) :-
	to_stack(Name,'$labeling_step'(X,Rel,Val,bisect)).

to_stack0(Name,backtrack_from_forced(X,Rel,Val)) :-
	to_stack(Name,'$labeling_step'(X,Rel,Val,bisect)).

to_stack(ASPName,'$labeling_step'(_,Rel,Val,bisect)) :-
	choice_stack([bisect(ASPName,Rel,Val)|_]),
	% just a change in the domain of the variable. No backtracking took place
	!.	%% needed because retract/1 is non-deterministic
%
%to_stack(ASPName) :-
%	choice_stack(Stack),
%	my_nth(Pos,Stack,ASPName),
%	!,
%	length(Stack,L_Stack),
%	L_Suffix is L_Stack - Pos,
%	length(Suffix,L_Suffix),
%	suffix(Suffix,Stack),
%	retract(choice_stack(Stack)),
%	assert(choice_stack([ASPName|Suffix])),
%show_stack,
%	!.	%% needed because retract/1 is non-deterministic
%%
to_stack(ASPName,'$labeling_step'(_,Rel,Val,bisect)) :-
	choice_stack(Stack),
	inverse_entry(bisect(ASPName,Rel,Val),InvEntry),
	my_nth(Pos,Stack,InvEntry),
	!,
	write('in backtrack of: '),write(bisect(ASPName,Rel,Val)),write('; '), write(InvEntry),write(' at pos '), write(Pos), nl,
	length(Stack,L_Stack),
	L_Suffix is L_Stack - Pos,
	length(Suffix,L_Suffix),
	suffix(Suffix,Stack),
	retract(choice_stack(Stack)),
write([bisect(ASPName,Rel,Val)|Suffix]),nl,
	assert(choice_stack([bisect(ASPName,Rel,Val)|Suffix])),
%	retract(choice_stack(Stack)),
%	assert(choice_stack([ASPName|Stack])),
show_stack,
	!.	%% needed because retract/1 is non-deterministic
to_stack(ASPName,'$labeling_step'(_,Rel,Val,bisect)) :-
	retract(choice_stack(Stack)),
	assert(choice_stack([bisect(ASPName,Rel,Val)|Stack])),
show_stack,
	!.	%% needed because retract/1 is non-deterministic

% backtrack up to and INCLUDING ASPName
backtrack_stack(ASPName) :-
write('PROBLEM!!! backtrack_stack not properly implemented yet!!!'),nl.
%	choice_stack(Stack),
%	my_nth(Pos,Stack,ASPName),
%	!,
%	length(Stack,L_Stack),
%	L_Suffix is L_Stack - Pos,
%	length(Suffix,L_Suffix),
%	suffix(Suffix,Stack),
%	retract(choice_stack(Stack)),
%	assert(choice_stack(Suffix)),
%show_stack,
%	!.	%% needed because retract/1 is non-deterministic



my_fdbg_show(Constraint, Actions) :-
	fdbg_annotate(Constraint, Actions, AnnotC, CVars),
	print(fdbg_output, AnnotC),
	nl(fdbg_output),
	fdbg_legend(CVars, Actions),
	nl(fdbg_output).

my_fdbg_label_show(start, I, Var) :-
	fdbg_annotate(Var, AVar, _),
	( AVar = fdvar(NameX, _, Set)
	-> fdset_to_range(Set, Range),
	   get_fdvar_name(NameX,Name),
%to_stack(Name),
	   format(fdbg_output,
		  'Labeling [~p, <~p>]: starting in range ~p.~n',
		  [I,Name,Range])
	; format(fdbg_output,
		 'Labeling [~p, <>]: starting.~n',
		 [I])
	).

my_fdbg_label_show(fail, I, Var) :-
	( var(Var)
	-> fdbg_annotate(Var, fdvar(NameX,_,_) , _),
	   get_fdvar_name(NameX,Name),
backtrack_stack(Name),
	   format(fdbg_output,
		  'Labeling [~p, <~p>]: failed.~n~n',
		  [I,Name])
	; format(fdbg_output,
		 'Labeling [~p, <>]: failed.~n~n',
		 [I])
	).

my_fdbg_label_show(step(Step), I, Var) :-
	( var(Var)
	-> fdbg_annotate(Var, fdvar(NameX,_,_) , _),
	   get_fdvar_name(NameX,Name),
to_stack0(Name,Step),
write('fd_dom is '),fd_dom(Var,Dom),write(Dom),nl,
write('fd_min is '),fd_min(Var,Min),write(Min),nl,
write('fd_max is '),fd_max(Var,Max),write(Max),nl,
write('step is '),write(Step),nl,
	   format(fdbg_output,
		  'Labeling [~p, <~p>]: ~p~n~n',
		  [I,Name,Step])
	; 
	format(fdbg_output,
		 'Labeling [~p, <>]: ~p~n~n',
		 [I,Step])
	).
