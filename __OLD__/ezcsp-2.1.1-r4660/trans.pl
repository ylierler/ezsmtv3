%
% By Marcello Balduccini [102208]
%
% Copyright (C) 2009-2021 Marcello Balduccini. All Rights Reserved.
%


:- use_module(library(system)).
:- use_module(library(lists)).
:- use_module(library(charsio)).
:- use_module(library(terms)).


:- use_module(library(timeout)).


:- use_module(library(codesio)).	% charsio was renamed in Sicstus4



sicstus4 :- current_module(codesio).
%
my_write_to_chars(X,Y) :- sicstus4, write_to_codes(X,Y).
my_write_to_chars(X,Y) :- \+ sicstus4, write_to_chars(X,Y).
%
my_nth(X,Y,Z) :- sicstus4, nth1(X,Y,Z).
my_nth(X,Y,Z) :- \+ sicstus4, nth(X,Y,Z).

translate_batch :-
	%nofileerrors,
	set_prolog_flag(fileerrors,off),
	nodebug,
	set_prolog_flag(unknown,fail),
	write('=-=-=-=-='),nl,
	translate,
        halt.

translate_batch :-  % batch must always succeed.
        write('++failed'),nl,
        halt.


parse(CSPDomain,Vars,Mapping,Domains,Constraints,LabelOptions) :-
	parse_cspdomain(CSPDomain),
	parse_cspvar(CSPDomain,Mapping,UnorderedVars,Domains),
	parse_required(CSPDomain,Mapping,Constraints),
	parse_label_order(Mapping,UnorderedVars,LabelOrder,Vars),
	parse_label_options(LabelOptions).



% [marcy 041510]
% translate currently supports only CSPDomain fd!!!
%
translate([CLPsolver,Clause]) :-
	parse(CSPDomain,Vars,Mapping,Domains,Constraints,LabelOptions),
	prepare_cspdomain(CSPDomain,CLPsolver),
	prepare_varlist(Vars,Body0),
	prepare_domains(Domains,Vars,Body1,DomainClauses),
	prepare_constraints(Constraints,Vars,Body2,ConstraintClauses),
	prepare_labeling(Vars,LabelOrder,LabelOptions,Body3),
	prepare_ifx_mapping(Mapping,Vars,Body4,MappingClauses,ResMapping),
	append(Body0,Body1,Body01),
	append(Body01,Body2,Body012),
	append(Body012,Body3,Body0123),
	append(Body0123,Body4,Body01234),
	turn_into_commas(Body01234,Body),
	Clause = ( solve(ResMapping) :- Body ),
	append(DomainClauses,ConstraintClauses,AllClauses1),
	append(AllClauses1,MappingClauses,AllClauses),
	portray_clauses([(:- CLPsolver),(:-use_module(library(lists))),Clause|AllClauses]).

translate :-
	translate(_).


%
% Called by exec.pl's batch & co. predicates when we are
% running the translation and execution steps together.
% In that case, predicate translate/1 above is NOT called.
%
solve(FinalMapping) :-
	parse(CSPDomain,Vars,Mapping,Domains,Constraints,LabelOptions),
	prepare_cspdomain(CSPDomain,CLPsolver),
	CLPsolver,
	use_module(library(lists)),
	prepare_varlist(Vars,Body0),
	run_domains(CSPDomain,Domains,Vars,Body1,DomainClauses),
	run_constraints(CSPDomain,Constraints,Vars,Body2,ConstraintClauses),
	run_labeling(CSPDomain,Vars,LabelOrder,LabelOptions,Body3,Mapping,FinalMapping).


parse_cspdomain(D) :-
	cspdomain(D),
	!.
%
parse_cspdomain(fd).	% now we use the FD domain by default
%parse_cspdomain(_) :-
%	write('No CSP domain specified with ASP relation cspdomain(_). Unable to proceed.'),nl,
%	fail.



parse_cspvar(CSPDomain,Mapping,Vars,Domains) :-
	findall_or_empty((ASPName,MinRange,MaxRange),cspvar(ASPName,MinRange,MaxRange),Decl),
	%
	length(Decl,N),
	length(Vars,N),
	%
	(CSPDomain = fd -> 
		fdbg_assign_name(Vars,myvars)	%%% [marcy 021810]
	 ;
	 	true
	),
	%
	form_mapping(Decl,Vars,UnsortedMapping),
	% sort to ensure that the result of form_var_list() 
	% always corresponds to a sorted list of ASPNames.
  	sort(UnsortedMapping,Mapping),
	form_domains(Decl,Vars,Domains).
%
form_mapping([],_,[]).
%
form_mapping([(ASPName,_,_)|DeclTail],[Var|VarTail],[(ASPName,Var)|MapTail]) :-
	form_mapping(DeclTail,VarTail,MapTail).
%
form_domains([],_,[]).
%
form_domains([(_,MinRange,MaxRange)|DeclTail],[Var|VarTail],[(Var,MinRange,MaxRange)|DomTail]) :-
	form_domains(DeclTail,VarTail,DomTail).


get_vars_objvar(VarsV) :-
	numbervars(VarsV,10000,_).


get_var(ASPName,Mapping,Var) :-
	my_nth(_,Mapping,(ASPName,Var)).


get_var_and_element(ASPName,Mapping,Var,(ASPName,Var)) :-
	my_nth(_,Mapping,(ASPName,Var)).

get_index(Var,Vars,N) :-
%	my_nth(N,Vars,Var).
%	write_to_chars(Var,[_|IndexChars]), number_chars(N,IndexChars).
	var_nth(N,Vars,Var).

%
% A variant of nth/3 that correctly matches
% variables by their NAME. For example:
%
%    var_nth(N,[X,Y],Y) succeeds for N=2
%
% while
%
%    my_nth(N,[X,Y],Y) succeeds for N=1,2.
%
var_nth(N,Vars,Var) :-
	var_nth(Var,Vars,1,N).

var_nth(Var,[Elem|_],N,N) :-
	var_is_same(Var,Elem),
	my_write_to_chars(Var,AnonymChars),
	my_write_to_chars(Elem,AnonymChars),
	!.

var_nth(Var,[_|Tail],I,N) :-
	I2 is I + 1,
	var_nth(Var,Tail,I2,N).

%
% Check if two specified variables have the same NAME.
%
var_is_same(VA,VB) :-
	my_write_to_chars(VA,AnonymChars),
	my_write_to_chars(VB,AnonymChars).


is_csp_variable((FuncSym,Arity),Mapping) :-
	FuncSym =.. [ASPFunc|GivenArgs],
	length(GivenArgs,NgivenArgs),
	NmissingArgs is Arity - NgivenArgs,
	length(MissingArgs,NmissingArgs),
	append(GivenArgs,MissingArgs,ARGS),
	ASPName =.. [ASPFunc|ARGS],
	get_var(ASPName,Mapping,_).



parse_required(CSPDomain,Mapping,Constraints) :-
	findall_or_empty(CONSTR,required(CONSTR),CONSTRlist),
	parse_constraints(CSPDomain,CONSTRlist,Mapping,Constraints).


parse_constraints(CSPDomain,[CONSTR|CONSTRlist],Mapping,[TransConstraint|Constraints]) :-
%	write('translating constraint: '),write(CONSTR),nl,
	CONSTR =.. [REL|ARGS],
%	write('rel args: '),write(REL),write('|'),write(ARGS),nl,
	parse_constraint(CSPDomain,REL,ARGS,Mapping,TransConstraint),
%	write('  translated constraint: '),write(TransConstraint),nl,
	parse_constraints(CSPDomain,CONSTRlist,Mapping,Constraints).

parse_constraints(_,[],_,[]).


% unary constraints
parse_constraint(CSPDomain,REL,[EXPR],Mapping,Constraint) :-
	is_local_constraint(REL),
	!,	% prevent from backtracking into 'catch-all' rule below
	map_local_constraint(CSPDomain,REL,CSPrel),
	map_expr(EXPR,Mapping,CSPexpr),
	Constraint =.. [CSPrel,CSPexpr].

% binary constraints
parse_constraint(CSPDomain,REL,[EXPR1,EXPR2],Mapping,Constraint) :-
	is_local_constraint(REL),
	!,	% prevent from backtracking into 'catch-all' rule below
	map_local_constraint(CSPDomain,REL,CSPrel),
	map_expr(EXPR1,Mapping,CSPexpr1),
	map_expr(EXPR2,Mapping,CSPexpr2),
	Constraint =.. [CSPrel,CSPexpr1,CSPexpr2].

parse_constraint(_,REL,ARGS,Mapping,Constraint) :-
	is_global_constraint(REL,ARGS),
	!,	% prevent from backtracking into 'catch-all' rule below
	map_global_constraint(REL,ARGS,PLREL),
	process_global_args(REL,ARGS,Mapping,CONSTRargs),
	Constraint =.. [PLREL|CONSTRargs].


parse_constraint(_,OTHER_CONSTR,ARGS,_,_) :-
	Atom =.. [OTHER_CONSTR|ARGS],
	write('***unhandled constraint: '),write(Atom),nl,
	fail.


is_global_constraint(REL,ARGS) :-
	length(ARGS,Nargs),
	global_constraint_spec(REL,Nargs,_).


process_global_args(REL,ARGS,Mapping,CONSTRargs) :-
	length(ARGS,Arity),
	global_constraint_spec(REL,Arity,ARGspecs),
	process_global_args(REL,ARGspecs,ARGS,Mapping,CONSTRargs).
%
process_global_args(REL,[ARGspec|ARGspecs],[ARG|ARGS],Mapping,[CONSTRarg|CONSTRargs]) :-
	process_global_arg(ARGspec,ARG,Mapping,CONSTRarg),
	process_global_args(REL,ARGspecs,ARGS,Mapping,CONSTRargs).
%
process_global_args(_,[],_,_,[]).



%
% NOTICE: FuncSym can be a compound term. In this case,
%         that means the first, given arguments are fixed.
%         E.g. list(f(a),2) means all terms of the form
%                        f(a,t)
%         where t is a term.
%
process_global_arg(_,list(FuncSym,Arity),Mapping,CONSTRarg) :-
	is_csp_variable((FuncSym,Arity),Mapping),
	!,  % to avoid the next case: list(RelSym,Arity)
	form_var_list((FuncSym,Arity),Mapping,CONSTRarg).

%
% NOTICE: RelSym can be a compound term. In this case,
%         that means the first, given arguments are fixed.
%         E.g. list(f(a),2) means all terms of the form
%                        f(a,t)
%         where t is a term.
%
process_global_arg(_,list(RelSym,Arity),_,CONSTRarg) :-
	form_rel_value_list((RelSym,Arity),CONSTRarg),
	!.  % to avoid the final 'catch-all' case.

% process extensively-represented lists
process_global_arg(_,ExtList,Mapping,CONSTRarg) :-
	ExtList =.. [extlist|List],
	form_gen_list(List,Mapping,CONSTRarg),
	!.  % to avoid the final 'catch-all' case.

process_global_arg(_,REL,_,CSPrel) :-
	map_local_constraint(fd,REL,CSPrel),	% specify fd because we are in the context of finite domains
	!.  % to avoid the next 'catch-all' case.

process_global_arg(_,ARG,Mapping,CONSTRarg) :-
	map_expr(ARG,Mapping,CONSTRarg).


% The result (3rd arg) is always sorted w.r.t. to the
% corresponding ASPNames because of the sort() in parse_cspvar().
%
form_var_list(_,[],[]).
%
form_var_list((FuncSym,Arity),[(ASPName,Var)|MapTail],[Var|VTail]) :-
	FuncSym =.. [ASPFunc|GivenArgs],
	length(GivenArgs,NgivenArgs),
	NmissingArgs is Arity - NgivenArgs,
	length(MissingArgs,NmissingArgs),
	append(GivenArgs,MissingArgs,ARGS),
	ASPName =.. [ASPFunc|ARGS],
	!, % avoid the next 'default' case
	form_var_list((FuncSym,Arity),MapTail,VTail).
%
form_var_list((FuncSym,Arity),[_|MapTail],VTail) :-
	form_var_list((FuncSym,Arity),MapTail,VTail).


form_gen_list([],_,[]).
%
form_gen_list([Item|ITail],Mapping,[Var|VTail]) :-
	Item =.. [FuncSym|Args],
	length(Args,Arity),
	is_csp_variable((Item,Arity),Mapping),
	!, % avoid the next 'default' case
	form_var_list((Item,Arity),Mapping,[Var]),
	form_gen_list(ITail,Mapping,VTail).
%
form_gen_list([Item|ITail],Mapping,[Item|VTail]) :-
	Item =.. [FuncSym], % no args -- constant
	!, % avoid the next 'default' case
	form_gen_list(ITail,Mapping,VTail).
%
form_gen_list([Item|ITail],Mapping,[Val|VTail]) :-
	Item =.. [FuncSym|Args],
	length(Args,Arity),
	form_rel_value_list((Item,Arity),[Val]),
	form_gen_list(ITail,Mapping,VTail).


form_rel_value_list((RelSym,Arity),ValList) :-
	RelSym =.. [ASPFunc|GivenArgs],
	length(GivenArgs,NgivenArgs),
	NmissingArgs is Arity - NgivenArgs,
	length(MissingArgs,NmissingArgs),
	append(GivenArgs,MissingArgs,ARGS),
	GenTerm =.. [ASPFunc|ARGS],
	findall_or_empty(GenTerm,GenTerm,UnsortedTermList),
	sort(UnsortedTermList,TermList),
	extract_list_of_last_args(TermList,ValList).

extract_list_of_last_args([Term|Terms],[Val|ValList]) :-
	Term =.. [_|Args],
	last(Args,Val),
	extract_list_of_last_args(Terms,ValList).

extract_list_of_last_args([],[]).


% My version of findall, which does not fail
% if the Template is not found.
%
findall_or_empty(Item,Template,List) :-
	current_prolog_flag(unknown,Old),
	set_prolog_flag(unknown,fail),
	findall(Item,Template,List),
	set_prolog_flag(unknown,Old).



map_expr(ASPName,Mapping,Var) :-
	get_var(ASPName,Mapping,Var),
	% Then it's just a CSP variable.
	% Avoid the 'default' case below.
	!.

map_expr(Const,_,Const) :-
%	\+ compound(Const),	% just \+ compound won't catch non-numerical constants as errors, although they normally are.
	number(Const),
	!.

map_expr(EXPR,Mapping,CSPexpr) :-
	compound(EXPR),
	EXPR =.. [Func|Args],
	%write('got expr: '),write(EXPR),nl,
	% the following disjunction is because of
	% reified constraints.
	( map_csp_function(Func,CSPfunc) ; map_local_constraint(fd,Func,CSPfunc) ), % specify fd because reified constraints allowed only in finite domains
	!,
	map_exprs(Args,Mapping,CSPargs),
	CSPexpr =.. [CSPfunc|CSPargs].
	%write('CSP expr is: '),write(CSPexpr),nl.

map_expr(EXPR,_,_) :-
	write('***unhandled expression '),write(EXPR),nl,
	fail.



map_exprs([Expr|ETail],Mapping,[CSPexpr|CSPTail]) :-
	map_expr(Expr,Mapping,CSPexpr),
	map_exprs(ETail,Mapping,CSPTail).
map_exprs([],_,[]).


map_asp_to_csp_order_list_and_unused([],_,Unused,[],Unused).

map_asp_to_csp_order_list_and_unused([(Num,ASPName)|ASPTail],Mapping,UnusedSoFar,[Num-Var|CSPTail],Unused) :-
	get_var_and_element(ASPName,Mapping,Var,Element),
	delete(UnusedSoFar,Element,Residue),
	map_asp_to_csp_order_list_and_unused(ASPTail,Mapping,Residue,CSPTail,Unused).


parse_label_order(Mapping,Vars,CSPOrderList,OrderedVars) :-
	findall_or_empty((Num,ASPName),label_order(ASPName,Num),ASPOrderListManual),
	dors_check_stack_dump(ASPOrderListManual,ASPOrderList), %%% [marcy 021810]
	map_asp_to_csp_order_list_and_unused(ASPOrderList,Mapping,Mapping,CSPOrderList,UnusedMapping),
%	map_asp_to_csp_order_list(ASPOrderList,Mapping,CSPOrderList),
	keysort(CSPOrderList,SortedOrder),
	extract_variables(SortedOrder,SpecifiedVars),
	extract_variables_from_mapping(UnusedMapping,UnspecifiedVars),
%	list_diff(Vars,SpecifiedVars,UnspecifiedVars),
	append(SpecifiedVars,UnspecifiedVars,OrderedVars).

extract_variables([],[]).

extract_variables([(_-Var)|PairTail],[Var|VarTail]) :-
	extract_variables(PairTail,VarTail).

extract_variables_from_mapping([],[]).

extract_variables_from_mapping([(_,Var)|Tail],[Var|VarTail]) :-
	extract_variables_from_mapping(Tail,VarTail).

%list_diff(List,[],List).
%
%list_diff(List,[Elem|RemoveTail],RemovedList) :-
%	var_delete(List,Elem,List2),
%	list_diff(List2,RemoveTail,RemovedList).

%
% variant of delete/3 that works properly with
% lists of anonymous variables.
%
% NOTE: var_delete/3 deletes a SINGLE occurrence.
%
var_delete([],_,[]).

var_delete([A|Tail],B,Tail) :-
	var_is_same(A,B),
	!.

var_delete([A|Tail],B,[A|Res]) :-
	var_delete(Tail,B,Res).



parse_label_options(LabelOptions) :-
	findall_or_empty(Opt,( label_option(RawOpt), map_csp_function(RawOpt,Opt) ),LabelOptions).



prepare_cspdomain(fd,(use_module(library(clpfd)))).
%
prepare_cspdomain(q,(use_module(library(clpq)))).
%
prepare_cspdomain(r,(use_module(library(clpr)))).


prepare_varlist(Vars,[( length(VarsV,N) )] ) :-
	length(Vars,N),
	get_vars_objvar(VarsV).


prepare_domains([],_,[],
		[(dom(VN,VarsV,MinRange,MaxRange) :- nth1(VN,VarsV,V), domain([V],MinRange,MaxRange)) ]) :- sicstus4.
%
prepare_domains([],_,[],
		[(dom(VN,VarsV,MinRange,MaxRange) :- nth(VN,VarsV,V), domain([V],MinRange,MaxRange)) ]) :- \+ sicstus4.
%
prepare_domains([(Var,MinRange,MaxRange)|DomTail],Vars,
		[dom(VN,VarsV,MinRange,MaxRange)|Body],
		DomainClauses):-
	length(DomTail,N),
	get_index(Var,Vars,VN),
	get_vars_objvar(VarsV),
	prepare_domains(DomTail,Vars,Body,DomainClauses).


run_domains(_,[],_,[],[]).
%
run_domains(fd,[(Var,MinRange,MaxRange)|DomTail],_,
		[],
		DomainClauses):-
	domain([Var],MinRange,MaxRange),
	run_domains(fd,DomTail,Vars,Body,DomainClauses).
%
run_domains(CSPDomain,[(Var,MinRange,MaxRange)|DomTail],_,
		[],
		DomainClauses):-
	( CSPDomain = r ; CSPDomain = q ),
	{ Var >= MinRange, Var =< MaxRange },
	run_domains(CSPDomain,DomTail,Vars,Body,DomainClauses).


prepare_constraints([],_,[],[]).
%
prepare_constraints([Constraint|Constraints],Vars,[constr(N,VarsV)|Calls],[(constr(N,VV) :- Body)|ConstraintClauses]) :-
	length(Constraints,N),
	get_vars_objvar(VarsV),
	term_variables(Constraint,ConstraintVars),
	form_nths(ConstraintVars,Vars,VV,NTHS),
	append(NTHS,[Constraint],BodyList),
	turn_into_commas(BodyList,Body),
	prepare_constraints(Constraints,Vars,Calls,ConstraintClauses).

form_nths([],_,_,[]).
%
form_nths([Var|VarTail],Vars,VV,[nth1(Index,VV,Var)|NTHTail]) :-
	sicstus4,
	get_index(Var,Vars,Index),
	form_nths(VarTail,Vars,VV,NTHTail).
%
form_nths([Var|VarTail],Vars,VV,[nth(Index,VV,Var)|NTHTail]) :-
	\+ sicstus4,
	get_index(Var,Vars,Index),
	form_nths(VarTail,Vars,VV,NTHTail).


run_constraints(_,[],_,[],[]).
%
run_constraints(fd,[Constraint|Constraints],Vars,Calls,ConstraintClauses) :-
	Constraint,
	run_constraints(fd,Constraints,Vars,Calls,ConstraintClauses).
%
run_constraints(CSPDomain,[Constraint|Constraints],Vars,Calls,ConstraintClauses) :-
	( CSPDomain = r ; CSPDomain = q ),
	{ Constraint },
	run_constraints(CSPDomain,Constraints,Vars,Calls,ConstraintClauses).


%
% WARNING [marcy 022510]
% Currently, prepare_labeling does not support using saved stacks.
%
prepare_labeling(Vars,_,LabelOptions,[labeling(LabelOptions,VarsV)]) :-
	get_vars_objvar(VarsV).


delete_var_sel([Option|LabelOptionsIN],LabelOptionsOUT) :-
	( Option = leftmost ;
	  Option = ff ;
	  Option = ffc ;
	  Option = min ;
	  Option = max ;
	  Option = variable(_)
	),
	!,
	delete_var_sel(LabelOptionsIN,LabelOptionsOUT).

delete_var_sel([Option|LabelOptionsIN],[Option|LabelOptionsOUT]) :-
	delete_var_sel(LabelOptionsIN,LabelOptionsOUT).

delete_var_sel([],[]).

to_csp_rel(<,#<).
to_csp_rel(>,#>).
to_csp_rel(=<,#=<).
to_csp_rel(>=,#>=).

invert_rel(<,>=).
invert_rel(>,=<).
invert_rel(>=,<).
invert_rel(=<,>).

my_enum(_,X,Rest,BB0,BB) :-
	dors_stack(loaded),
	dors_stack_type(single),
	fdbg_annotate(X, fdvar(NameX,_,_) , _),
	get_fdvar_name(NameX,Name),
	\+ dors_stack_in([bisect(Name,Rel,Val)|_]),
	write('***PROBLEM: my_enum decision at top of stack not about variable '), write(Name),nl,
	fail.

my_enum(_,X,Rest,BB0,BB) :-
	dors_stack(loaded),
	dors_stack_type(single),
	fdbg_annotate(X, fdvar(NameX,_,_) , _),
	get_fdvar_name(NameX,Name),
	retract(dors_stack_in([bisect(Name,Rel,Val)|Stack])),
	!,
	(
		assert(dors_stack_in(Stack)),
		clpfd:fdbg_labeling_step(X,forced(Name,Rel,Val)),
		first_bound(BB0,BB),
		to_csp_rel(Rel,CSPRel),
		CSPConstraint =.. [CSPRel,X,Val],
		CSPConstraint
	;
		invert_rel(Rel,InvRel),
		clpfd:fdbg_labeling_step(X,backtrack_from_forced(Name,InvRel,Val)),
		later_bound(BB0,BB),
		to_csp_rel(InvRel,CSPRel),
		CSPConstraint =.. [CSPRel,X,Val],
		CSPConstraint
	).

my_enum(_,X,Rest,BB0,BB) :-
	dors_stack(loaded),
	dors_stack_type(merged),
	fdbg_annotate(X, fdvar(NameX,_,_) , _),
	get_fdvar_name(NameX,Name),
	get_merged_choice_for_var(X,Name,Rel,Val),
	!,
	(
		clpfd:fdbg_labeling_step(X,forced(Name,Rel,Val)),
		first_bound(BB0,BB),
		to_csp_rel(Rel,CSPRel),
		CSPConstraint =.. [CSPRel,X,Val],
		CSPConstraint
	;
		invert_rel(Rel,InvRel),
		clpfd:fdbg_labeling_step(X,backtrack_from_forced(Name,InvRel,Val)),
		later_bound(BB0,BB),
		to_csp_rel(InvRel,CSPRel),
		CSPConstraint =.. [CSPRel,X,Val],
		CSPConstraint
	).

get_merged_choice_for_var(V,Name,Rel,Val) :-
	dors_stack_in(Stack),
	current_decision_level(DLevel),
	
	level_choices(Stack,DLevel,Choices),

	best_choice_for_var(V,Name,Choices,Rel,Val).

my_enum(up,X,Rest,BB0,BB) :-
%	fdbg_annotate(X, fdvar(NameX,_,_) , _),
%	get_fdvar_name(NameX,Name),
%	write(Name),write(' in my enum1'),nl,
	fd_min(X,Min),
	fd_max(X,Max),
	Midpoint is (Min + Max) // 2,
	clpfd:fdbg_labeling_step(X,'$labeling_step'(var,=<,Midpoint,bisect)),
	first_bound(BB0,BB),
	%X in Min .. Midpoint.
	#=<(X,Midpoint).
%
% IMPORTANT: as far as I understand, 
%            clpfd:fdbg_start_labeling(X) is called by labeling/2,
%            and should be called by custom replacements of labeling/2.
%            We don't need to call it from my_emu/5.
%
%	clpfd:fdbg_start_labeling(X).

my_enum(up,X,Rest,BB0,BB) :-
%	fdbg_annotate(X, fdvar(NameX,_,_) , _),
%	get_fdvar_name(NameX,Name),
%	write(Name),write(' in my enum2'),nl,
	fd_min(X,Min),
	fd_max(X,Max),
	Midpoint is (Min + Max) // 2,
	clpfd:fdbg_labeling_step(X,'$labeling_step'(var,>,Midpoint,bisect)),
	later_bound(BB0,BB),
	#>(X,Midpoint).
	%X in Midpoint .. Max.

my_enum(down,X,Rest,BB0,BB) :-
%	fdbg_annotate(X, fdvar(NameX,_,_) , _),
%	get_fdvar_name(NameX,Name),
%	write(Name),write(' in my enum1'),nl,
	fd_min(X,Min),
	fd_max(X,Max),
	Midpoint is (Min + Max) // 2 + 1,
	clpfd:fdbg_labeling_step(X,'$labeling_step'(var,>=,Midpoint,bisect)),
	first_bound(BB0,BB),
	%X in Min .. Midpoint.
	#>=(X,Midpoint).
%
% IMPORTANT: as far as I understand, 
%            clpfd:fdbg_start_labeling(X) is called by labeling/2,
%            and should be called by custom replacements of labeling/2.
%            We don't need to call it from my_emu/5.
%
%	clpfd:fdbg_start_labeling(X).

my_enum(down,X,Rest,BB0,BB) :-
%	fdbg_annotate(X, fdvar(NameX,_,_) , _),
%	get_fdvar_name(NameX,Name),
%	write(Name),write(' in my enum2'),nl,
	fd_min(X,Min),
	fd_max(X,Max),
	Midpoint is (Min + Max) // 2 + 1,
	clpfd:fdbg_labeling_step(X,'$labeling_step'(var,<,Midpoint,bisect)),
	later_bound(BB0,BB),
	#<(X,Midpoint).
	%X in Midpoint .. Max.

get_var_from_fdname(FDName,[V|_],V) :-
	fdbg_annotate(V, fdvar(FDName,_,_) , _),
	!.

get_var_from_fdname(FDName,[_|Vars],V) :-
	get_var_from_fdname(FDName,Vars,V).

get_var_from_fdname(FDName,[],_) :-
	write('***PROBLEM: cannot find variable for fdname '),write(FDName),nl,
	fail.
	

my_sel(_,Vars, V, NewVars) :-
	dors_stack(loaded),
	dors_stack_type(single),
	dors_stack_in([bisect(Name,Rel,Val)|Tail]),
write('selecting '),writeq(Name),nl,
	get_fdvar_name(FDName,Name),
	get_var_from_fdname(FDName,Vars,V),
	( Tail = [] -> NewVars=[]; NewVars=Vars),
	!.	% my_sel is required to be deterministic

my_sel(_,Vars, V, NewVars) :-
	dors_stack(loaded),
	dors_stack_type(single),
	dors_stack_in([bisect(Name,Rel,Val)|Tail]),
	% If the previous clause backtracked, then that means
	% that the variable at the top of the stack has already
	% been assigned a value.
write('latest my_sel variable has been assigned a value. Skipping it.'),nl,
	retract(dors_stack_in([bisect(Name,Rel,Val)|Stack])),
	assert(dors_stack_in(Stack)),
	!,
	my_sel(_,Vars, V, NewVars).

my_sel(_,Vars, V, Rest) :-
	dors_stack(loaded),
	dors_stack_type(merged),
	get_merged_choice(Vars,Name,V,Rest),
	!,
write('selecting '),writeq(Name),nl.

get_merged_choice(Vars,Name,V,Vars) :-
	dors_stack_in(Stack),
	current_decision_level(DLevel),
	write('Decision level='),write(DLevel),nl,
	
	level_choices(Stack,DLevel,Choices),

	best_choice(Choices,Vars,V,Name).

current_decision_level(Level) :-
	choice_stack(Stack),
	length(Stack,Level0),
	Level is Level0 + 1.

level_choices([Choices|_],1,Choices).

level_choices([_|Stack],N,Choices) :-
	N > 1,
	N2 is N - 1,
	level_choices(Stack,N2,Choices).

already_satisfied(V,>,Val) :-   %%%---
	fd_min(V,Min),
	Val < Min.

already_satisfied(V,>,Val) :-   %%%---
	fd_max(V,Max),
	Val >= Max.

already_satisfied(V,>=,Val) :-
	fd_min(V,Min),
	Val =< Min.

already_satisfied(V,>=,Val) :-
	fd_max(V,Max),
	Val > Max.

already_satisfied(V,<,Val) :-
	fd_min(V,Min),
	Val =< Min.

already_satisfied(V,<,Val) :-
	fd_max(V,Max),
	Val > Max.

already_satisfied(V,=<,Val) :-
	fd_min(V,Min),
	Val < Min.

already_satisfied(V,=<,Val) :-
	fd_max(V,Max),
	Val >= Max.

% ASSUMPTION: choices in Choices are ordered
% in descending order of occurrence count.
best_choice_for_var(V,Name,[(bisect(Name,Rel,Val),_)|_],Rel,Val) :-
	%
	% Avoid choices that are already satisfied
	% (e.g. V>30 when V's range is already 50..80).
	% Not only those choices are useless, but they can also
	% fool our auto-detection of backtracking
	% (see predicate in_stack).
	%
	\+ already_satisfied(V,Rel,Val),
	!.
%
best_choice_for_var(V,Name,[(bisect2(Name,Rel),_)|_],Rel,Val) :-
	fd_min(X,Min),
	fd_max(X,Max),
	Val is (Min + Max) // 2,
	!.
%
best_choice_for_var(V,Name,[_|Choices],Rel,Val) :-
	best_choice_for_var(V,Name,Choices,Rel,Val).

% ASSUMPTION: choices in Choices are ordered
% in descending order of occurrence count.
best_choice([(bisect(Name,Rel,Val),_)|_],Vars,V,Name) :-
	get_fdvar_name(FDName,Name),
	get_var_from_fdname(FDName,Vars,V),
	\+ integer(V),
	%
	% Avoid choices that are already satisfied
	% (e.g. V>30 when V's range is already 50..80).
	% Not only those choices are useless, but they can also
	% fool our auto-detection of backtracking
	% (see predicate in_stack).
	%
	\+ already_satisfied(V,Rel,Val),
	fd_min(V,Min),
	fd_max(V,Max),
write('the choice is '),write((V,Rel,Val,range(Min,Max))),nl,
	!.
%
best_choice([(bisect2(Name,Rel),_)|_],Vars,V,Name) :-
	get_fdvar_name(FDName,Name),
	get_var_from_fdname(FDName,Vars,V),
	\+ integer(V),
	!.
%
best_choice([_|Choices],Vars,V,Name) :-
	best_choice(Choices,Vars,V,Name).


my_sel(leftmost,[V|Vars], V, Vars) :-
	write('***PROBLEM: my_sel is resorting to leftmost'),nl.

my_sel(ff,[V|Vars], X, Rest) :-
	write('***PROBLEM: my_sel is resorting to ff'),nl,
	fd_size(V,S),
	my_sel_ff(Vars,V,S,X,Rest).

my_sel_ff([],X,_,X,[]).

my_sel_ff([V|Vars],V0,S0,X,Rest) :-
	integer(V), !,
	my_sel_ff(Vars,V0,S0,X,Rest).

my_sel_ff([V|Vars],V0,S0,X,[Y|Rest]) :-
	fd_size(V,S),
	(	S < S0 -> Y=V0, my_sel_ff(Vars,V,S,X,Rest)
	;	Y=V, my_sel_ff(Vars,V0,S0,X,Rest)
	).

run_labeling(fd,Vars,_,LabelOptions,[],Mapping,Mapping) :-
	dors_store_fdvar_names(Mapping),	% [marcy 021810] asserts relation varmap
	( dors_stack(loaded) ->
		( write('using saved stack'),nl,
		  delete_var_sel(LabelOptions,LabelOptions2),
%		  labeling([leftmost|LabelOptions2],Vars) ) ; % [marcy 021810]
%---------------------
% IMPORTANT: when using value/1 option in labeling/2,
%            up and down must NOT be specified. Doing
%            so causes labeling/2 to fail without any
%            warning or error message.
% [marcy 030310]
%---------------------
		  labeling([variable(my_sel(ff)),value(my_enum(up)),all],Vars)
		)
		; % [marcy 021810]
		( write('using stack from program'),nl, labeling(LabelOptions,Vars)) % [marcy 021810]
	),
	dors_output_stack. % [marcy 021810]
%
run_labeling(CSPDomain,Vars,_,_,[],Mapping,FinalMapping) :-
	( CSPDomain = r ; CSPDomain = q ),
	form_final_mapping(Vars,Mapping,FinalMapping).

form_final_mapping(Q,Mapping,FinalMapping) :-
	remove_value_assigned(Q,Q2),
	value_assigned_mapping(Mapping,VMapping),
	form_final_mapping2(Q2,Mapping,RQMapping),
	append(VMapping,RQMapping,FinalMapping).

remove_value_assigned([],[]).
remove_value_assigned([V|Q],[V|Q2]) :-
	var(V),
	!,
	remove_value_assigned(Q,Q2).
remove_value_assigned([_|Q],Q2) :-
	remove_value_assigned(Q,Q2).

value_assigned_mapping([],[]).
value_assigned_mapping([(ASPName,V)|Mapping],[(ASPName,V)|VMapping]) :-
	\+ var(V),
	!,
	value_assigned_mapping(Mapping,VMapping).
value_assigned_mapping([_|Mapping],VMapping) :-
	value_assigned_mapping(Mapping,VMapping).


form_final_mapping2(Q, Mapping, A) :-
	dump(Q,V,C),
	rename_termlist(C,A,Q,V,Mapping).

rename_termlist([Arg|Args],[RenArg|RenArgs],Q,V,Mapping) :-
	rename_term(Arg,RenArg,Q,V,Mapping),
	rename_termlist(Args,RenArgs,Q,V,Mapping).

rename_termlist([],[],_,_,_).

rename_term(C,A,Q,V,Mapping) :-
	var(C),
	!,
	map_varsrq(C,A,Q,V,Mapping).

rename_term(C,C,Q,V,Mapping) :-
	\+ compound(C), !.

rename_term([],[],Q,V,Mapping) :-
	!.

rename_term(C,A,Q,V,Mapping) :-
	C =.. [FC|Args],
	map_varsrq(FC,FA,Q,V,Mapping),
	rename_termlist(Args,RenArgs,Q,V,Mapping),
	A =.. [FA|RenArgs].

map_varsrq(C,C,_,_,_) :-
	\+ var(C).

map_varsrq(C,A,Q,V,[(A,Var)|_]) :-
	var(C),
	my_nth(N,V,C),
	my_nth(N,Q,C2),
	var_is_same(C2,Var),
	!.

map_varsrq(C,A,Q,V,[_|Mapping]) :-
	var(C),
	map_varsrq(C,A,Q,V,Mapping).

map_varsrq(C,C,_,_,[]).


prepare_ifx_mapping(Mapping,Vars,
		   [form_result(VarsV,Names,ResMapping)],
		   [
		    ( form_result([],[],[]) ),
		    ( form_result([V|VarsTail],[Name|NTail],[(Name,V)|MTail]) :- form_result(VarsTail,NTail,MTail) )
		   ],
		   ResMapping
		   ) :-
	get_vars_objvar(VarsV),
	form_indexed_mapping(Mapping,Vars,IndexedMapping),
	keysort(IndexedMapping,SortedMappingByVars),
	extract_names(SortedMappingByVars,Names).

form_indexed_mapping([],_,[]).
%
form_indexed_mapping([(ASPName,Var)|Mapping],Vars,[Index-ASPName|IndexedMapping]) :-
	get_index(Var,Vars,Index),
	form_indexed_mapping(Mapping,Vars,IndexedMapping).

extract_names([],[]).
%
extract_names([_-ASPName|Mapping],[ASPName|Names]) :-
	extract_names(Mapping,Names).



portray_clauses([]).
%
portray_clauses([(:- Body)|Tail]) :-
	!,	% special pretty-printing for directives, which don't work well with portray_clause
	write(':- '), portray_clause(Body), nl,
	portray_clauses(Tail).
%	
portray_clauses([C|Tail]) :-
	portray_clause(C), nl,
	portray_clauses(Tail).




turn_into_commas([],true).
%
turn_into_commas([T],T).
%
turn_into_commas([T|Tail],(T,Rest)) :-
	turn_into_commas(Tail,Rest).


map_local_constraint(fd,ezcsp__lt,#<).
map_local_constraint(fd,ezcsp__gt,#>).
map_local_constraint(fd,ezcsp__leq,#=<).
map_local_constraint(fd,ezcsp__geq,#>=).
map_local_constraint(fd,ezcsp__eq,#=).
map_local_constraint(fd,ezcsp__neq,#\=).
map_local_constraint(fd,ezcsp__impl_r,#=>).
map_local_constraint(fd,ezcsp__impl_l,#<=).
map_local_constraint(fd,ezcsp__or,#\/).
map_local_constraint(fd,ezcsp__and,#/\).
map_local_constraint(fd,ezcsp__xor,#\).
map_local_constraint(fd,ezcsp__diff,#<=>).
map_local_constraint(fd,ezcsp__not,#\).
%
map_local_constraint(r,ezcsp__lt,<).
map_local_constraint(r,ezcsp__gt,>).
map_local_constraint(r,ezcsp__leq,=<).
map_local_constraint(r,ezcsp__geq,>=).
map_local_constraint(r,ezcsp__eq,=).
map_local_constraint(r,ezcsp__neq,\=).
map_local_constraint(r,ezcsp__impl_r,=>).
map_local_constraint(r,ezcsp__impl_l,<=).
map_local_constraint(r,ezcsp__or,\/).
map_local_constraint(r,ezcsp__and,/\).
map_local_constraint(r,ezcsp__xor,\).
map_local_constraint(r,ezcsp__diff,<=>).
map_local_constraint(r,ezcsp__not,\).
%
map_local_constraint(q,E,C) :-
	map_local_constraint(r,E,C).



map_csp_function(ezcsp__pl,+).
map_csp_function(ezcsp__mn,-).
map_csp_function(ezcsp__tm,*).
map_csp_function(ezcsp__dv,/).
map_csp_function(ezcsp__mod,mod).
map_csp_function(ezcsp__max,max).
map_csp_function(ezcsp__min,min).
map_csp_function(ezcsp__abs,abs).
map_csp_function(ezcsp__pow,pow).	% NEW FROM HERE
map_csp_function(ezcsp__exp,exp).
map_csp_function(ezcsp__sin,sin).
map_csp_function(ezcsp__cos,cos).
map_csp_function(ezcsp__tan,tan).




is_local_constraint(ezcsp__lt).
is_local_constraint(ezcsp__gt).
is_local_constraint(ezcsp__leq).
is_local_constraint(ezcsp__geq).
is_local_constraint(ezcsp__eq).
is_local_constraint(ezcsp__neq).
is_local_constraint(ezcsp__impl_r).
is_local_constraint(ezcsp__impl_l).
is_local_constraint(ezcsp__or).
is_local_constraint(ezcsp__and).
is_local_constraint(ezcsp__xor).
is_local_constraint(ezcsp__diff).
is_local_constraint(ezcsp__not).


is_list_var_rel(REL,ARGS) :-
	length(ARGS,Arity),
	list_CSP_rel(REL,Arity,_).


map_global_constraint(REL,ARGS,PLREL) :-
	length(ARGS,Nargs),
	map_global_constraint_nargs(REL,Nargs,PLREL),
	!.

map_global_constraint(REL,_,REL).


% name mapping for certain global constraints
map_global_constraint_nargs(ezcsp__sum,3,sum).
map_global_constraint_nargs(cumulative,4,abstr_cumulative) :- sicstus4.


%
% Allowed argument types:
%
%    csp: name of CSP function -- will be turned into a list.
%    asp: name of ASP (functional) relation -- will be turned into a list)
%    expr: expression, possibly containing CSP functions (CSP functions will be replaced by corresp. variables)
%    rel(MatchingRelation): CSP relation (e.g. ezcsp__gt) -- relation MatchingRelation will be used to map it to the appropriate CSP relation, e.g. rel(match_CSP_relation) may cause the use of match_CSP_relation(ezcsp__gt,#>).
%
global_constraint_spec(ezcsp__sum,3,[csp,rel(match_CSP_relation),expr]).
global_constraint_spec(minimum,2,[expr,csp]).
global_constraint_spec(maximum,2,[expr,csp]).
global_constraint_spec(scalar_product,4,[asp,csp,rel(match_CSP_relation),expr]).
global_constraint_spec(serialized,2,[csp,asp]).
global_constraint_spec(cumulative,4,[csp,asp,asp,expr]).
global_constraint_spec(disjoint2,4,[csp,asp,csp,asp]).
global_constraint_spec(all_different,1,[csp]).
global_constraint_spec(all_distinct,1,[csp]).
global_constraint_spec(count,4,[expr,csp,rel(match_CSP_relation),expr]).
global_constraint_spec(element,3,[expr,csp,expr]).
global_constraint_spec(assignment,2,[csp,csp]).
global_constraint_spec(circuit,1,[csp]).
global_constraint_spec(circuit,2,[csp,csp]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/*
% put cspdomain(fd) at the top of this file.
cspvar(st(0,c),0,200).
cspvar(st(1,c),0,200).
cspvar(st(2,c),0,200).
cspvar(st(0,b),0,200).
cspvar(st(1,b),0,200).
cspvar(st(2,b),0,200).
cspvar(st(0,a),0,200).
cspvar(st(1,a),0,200).
cspvar(st(2,a),0,200).
part_len(2,c,9).
part_len(2,b,8).
part_len(2,a,7).
part_len(1,c,6).
part_len(1,b,5).
part_len(1,a,4).
part_len(0,c,3).
part_len(0,b,2).
part_len(0,a,1).
r(2,c,1).
r(2,b,1).
r(2,a,1).
r(1,c,1).
r(1,b,1).
r(1,a,1).
r(0,c,1).
r(0,b,1).
r(0,a,1).
required(cumulative(st,f(part_len,3),r,1)).
*/
/*
% put cspdomain(fd) at the top of this file.
required(ezcsp__geq(st(0,c),ezcsp__pl(st(0,b),2))).
required(ezcsp__geq(st(1,c),ezcsp__pl(st(1,b),5))).
required(ezcsp__geq(st(2,c),ezcsp__pl(st(2,b),8))).
required(ezcsp__geq(st(0,b),ezcsp__pl(st(0,a),1))).
required(ezcsp__geq(st(1,b),ezcsp__pl(st(1,a),4))).
required(ezcsp__geq(st(2,b),ezcsp__pl(st(2,a),7))).
required(sum(st,ezcsp__lt,100)).
maezcsp__sum(8).
part_len(2,c,9).
part_len(2,b,8).
part_len(2,a,7).
part_len(1,c,6).
part_len(1,b,5).
part_len(1,a,4).
part_len(0,c,3).
part_len(0,b,2).
part_len(0,a,1).
precedes(b,c).
precedes(a,b).
part(c).
part(b).
part(a).
job(0).
job(1).
job(2).
cspvar(st(0,c),0,20).
cspvar(st(1,c),0,20).
cspvar(st(2,c),0,20).
cspvar(st(0,b),0,20).
cspvar(st(1,b),0,20).
cspvar(st(2,b),0,20).
cspvar(st(0,a),0,20).
cspvar(st(1,a),0,20).
cspvar(st(2,a),0,20).
%%endmodel
*/

