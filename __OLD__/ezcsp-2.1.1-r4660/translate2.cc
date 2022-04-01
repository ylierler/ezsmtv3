// by Marcello Balduccini [050709]
// Copyright (C) 2009-2021 Marcello Balduccini. All Rights Reserved.
//
// Translates a set of literals containing a CSP definition
// into the encoding suitable for the selected solver language.
// Each literal must be ground and followed by a "." (e.g. "mkatoms -a" format).
// Double-quotes can be used for quoting.
//
// Usage: translate <file1> [<file2>...]
//    or: translate    (with no arguments) to use standard input
//

#include "config.h"

#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <string.h>

#include <iostream>
#include <fstream>

#include <string>
#include <vector>
#include <algorithm>

#include <aspparser/parser.h>

#include "phpemu.h"

#include "common.h"

#include "TRAN/pp2.h"

#include "solver-types.h"

#include "library_notes.h"

#include "translate2.h"

#include "translate2_minizinc.h"

#include "translate2_gurobi.h"

using namespace std;
using namespace phpemu;

CSP *curr_csp;	/* for labelSort */


char *which_solver[]=
{	(char *)"which_solver(sicstus4).\n",	// CPSOLVER_SICSTUS4
	(char *)"which_solver(sicstus3).\n",	// CPSOLVER_SICSTUS3
	(char *)"which_solver(bprolog).\n",	// CPSOLVER_BPROLOG
	(char *)"which_solver(swiprolog).\n"	// CPSOLVER_SWIPROLOG
};

char *nth_rel[]=
{	(char *)"nth1",	// CPSOLVER_SICSTUS4
	(char *)"nth",	// CPSOLVER_SICSTUS3
	(char *)"nth",	// CPSOLVER_BPROLOG
	(char *)"nth1"	// CPSOLVER_SWIPROLOG
};

char *write_to_chars_rel[]=
{	(char *)"write_to_codes",	// CPSOLVER_SICSTUS4
	(char *)"write_to_chars",	// CPSOLVER_SICSTUS3
	(char *)"write_to_chars",	// CPSOLVER_BPROLOG
	(char *)"swipl_write_to_chars"	// CPSOLVER_SWIPROLOG
};

char *charsio_lib[]=
{	(char *)":- use_module(library(codesio)).\n",	// CPSOLVER_SICSTUS4
	(char *)":- use_module(library(charsio)).\n",	// CPSOLVER_SICSTUS3
	(char *)"",	// CPSOLVER_BPROLOG
	(char *)""	// CPSOLVER_SWIPROLOG
};

bool sameItem(const struct item * const & i1, const struct item * const & i2)
{	int j;

	if (i1->relation==NULL) return(false);

	if (i2->relation==NULL) return(false);

//clog << "got " << i1->relation << "; " << i2->relation << endl;

	j=strcmp(i1->relation,i2->relation);

	if (j!=0 || i1->arity!=i2->arity) return(false);
	
	for(j=0;j<i1->arity && j<i2->arity;j++)
		if (!sameItem(i1->args[j],i2->args[j])) return(false);

	return(true);
}

int get_label_order(CSP *csp,const struct item *i)
{	int v=hash_item::compute_hash_value(i);

	if ((int)csp->label_order_hash.size()<=v) return(-1);

	for(int j=0;j<(int)csp->label_order_hash[v].size();j++)
		if (sameItem(i,csp->label_order_hash[v][j]->i))
			return(csp->label_order_hash[v][j]->index);

	return(-1);
}

bool labelSort(const struct item * const & i1, const struct item * const & i2)
{	int i1_order=-1,i2_order=-1;


	i1_order=get_label_order(curr_csp,i1);
	i2_order=get_label_order(curr_csp,i2);
/*
	int j;

	for(j=0;j<(int)curr_csp->label_order.size();j++)
	{	if (sameItem(i1,curr_csp->label_order[j]->args[0]))
			i1_order=atoi(curr_csp->label_order[j]->args[1]->relation);
		else
		if (sameItem(i2,curr_csp->label_order[j]->args[0]))
			i2_order=atoi(curr_csp->label_order[j]->args[1]->relation);
	}
*/
	if (i1_order==-1) return(false);

	if (i2_order==-1) return(true);

	return (i1_order<i2_order);
}

void sort_labeling(CSP *csp)
{	curr_csp=csp;
	sort(csp->labeling.begin(), csp->labeling.end(), labelSort);
}


bool itemSort2(const struct item * const & i1, const struct item * const & i2,bool *same)
{	int j;

	if (same!=NULL) *same=false;

	if (i1->relation==NULL) return(true);

	if (i2->relation==NULL) return(false);

//clog << "got " << i1->relation << "; " << i2->relation << endl;

	j=strcmp(i1->relation,i2->relation);
	
	if (j<0) return(true);
	if (j>0) return(false);

	for(j=0;j<i1->arity && j<i2->arity;j++)
	{	bool arg_same;

		if (itemSort2(i1->args[j],i2->args[j],&arg_same)) return(true);
		if (!arg_same) return(false);
	}

	if (i1->arity<i2->arity) return(true);

	if (i1->arity==i2->arity && same!=NULL)
		*same=true;

	return(false);
}

bool itemSort(const struct item * const & i1, const struct item * const & i2)
{	return(itemSort2(i1,i2,NULL));
}

CSP *extract_csp(struct node *program)
{	struct node *n;

	CSP *csp;

	csp=new CSP;

	for(n=program->next;n!=NULL;n=n->next)
	{	struct item *fact;

		if (n->data->head_size!=1 || n->data->body_size!=0)
		{	clog << "ERROR: translate2 expects an answer set in input" <<endl;
			exit(1);
		}

		fact=n->data->head[0];
		csp->sorted_facts.push_back(fact);
	}
	sort(csp->sorted_facts.begin(), csp->sorted_facts.end(), itemSort);

	for(int i=0;i<(int)csp->sorted_facts.size();i++)
	{	struct item *fact;

		fact=csp->sorted_facts[i];

		if ((strcmp(fact->relation,"cspdomain")==0 || strcmp(fact->relation,"domain")==0)
		    && fact->arity==1)
		{	csp->domain=fact->args[0]->relation;
			if (csp->domain=="query") csp->domain="fd";	/* query is treated as a synonym of fd */
		}
		else
		if ((strcmp(fact->relation,"cspvar")==0 || strcmp(fact->relation,"var")==0)
		    && (fact->arity==3 || fact->arity==1))
		{	csp->cspvar.push_back(fact);
			csp->labeling.push_back(fact->args[0]);
		}
		else
		if (strcmp(fact->relation,"lpinteger")==0 && fact->arity==1)
		{	csp->lpinteger.push_back(fact);
		}
		else
		if (strcmp(fact->relation,"required")==0 && fact->arity==1)
			csp->required.push_back(fact);
		else
		if (strcmp(fact->relation,"lpobjective")==0 && fact->arity==1 &&
		    (strcmp(fact->args[0]->relation,"ezcsp__min")==0 || strcmp(fact->args[0]->relation,"ezcsp__max")==0) &&
		    fact->args[0]->arity==1)
			csp->objective=fact->args[0];
		else
		if(strcmp(fact->relation,"label_order")==0 && fact->arity==2)
		{	//csp->label_order.push_back(fact);

			struct hash_item *h=new hash_item(fact->args[0],atoi(fact->args[1]->relation));
			int v=h->compute_hash_value();

			if ((int)csp->label_order_hash.size()<=v)
				csp->label_order_hash.resize(v+1);
			csp->label_order_hash[v].push_back(h);
		}
		else
		if(strcmp(fact->relation,"label_option")==0 && fact->arity==1)
			csp->label_options.push_back(fact->args[0]->relation);
	}
	sort_labeling(csp);
	for(int i=0;i<(int)csp->labeling.size();i++)
	{	struct hash_item *h=new hash_item(csp->labeling[i],i+1);
		int v=h->compute_hash_value();

		if ((int)csp->labeling_hash.size()<=v)
			csp->labeling_hash.resize(v+1);
		csp->labeling_hash[v].push_back(h);
	}
	

	return(csp);
}

int get_var_index(CSP *csp,struct item *var)
{	int v=hash_item::compute_hash_value(var);

	if ((int)csp->labeling_hash.size()<=v) return(0);

	for(int i=0;i<(int)csp->labeling_hash[v].size();i++)
		if (sameItem(csp->labeling_hash[v][i]->i,var))
			return(csp->labeling_hash[v][i]->index);
/*
	for(int i=0;i<(int)csp->labeling.size();i++)
		if (sameItem(csp->labeling[i],var))
			return(i+1);
*/

	return(0);
}

/* pattern is list(<term>,<total arity>) */
bool item_matches_pattern(CSP *csp,struct item *i,struct item *pattern)
{
	if (i->relation==NULL) return(false);

	if (strcmp(pattern->relation,"list")!=0 || pattern->arity!=2) return(false);

	if (strcmp(pattern->args[0]->relation,i->relation)!=0) return(false);

	if (atoi(pattern->args[1]->relation)!=i->arity) return(false);

	for(int j=0;j<pattern->args[0]->arity;j++)
	{	if (!sameItem(pattern->args[0]->args[j],i->args[j])) return(false);
	}

	return(true);
}

void fix_item(struct item *a,CSP *csp,int cpsolver_type,bool allow_unsupported)
{	int i;

#define FOR_ANY_SOLVER	0
#define FOR_SICSTUS4	(1<<CPSOLVER_SICSTUS4)
#define FOR_SICSTUS3	(1<<CPSOLVER_SICSTUS3)
#define FOR_SICSTUS	(FOR_SICSTUS4|FOR_SICSTUS4)
#define FOR_BPROLOG	(1<<CPSOLVER_BPROLOG)
#define FOR_SWIPROLOG	(1<<CPSOLVER_SWIPROLOG)
#define FOR_GAMS	(1<<CPSOLVER_GAMS)
#define INVERT_ARGS	0x0100	/* must invert the order of the args */
#define UNSUPPORTED	0x0200	/* not supported by the solver. Will cause an error in EZCSP unless --allow-unsupported is given */

	struct syntax_map map_fd[]=
	{	{ (char *)"#>", (char *)"ezcsp__gt", FOR_ANY_SOLVER, false },

		{ (char *)"#>=", (char *)"ezcsp__geq", FOR_ANY_SOLVER, false },

		{ (char *)"#<", (char *)"ezcsp__lt", FOR_ANY_SOLVER, false },

		{ (char *)"#=<", (char *)"ezcsp__leq", FOR_ANY_SOLVER, false },

		{ (char *)"#=", (char *)"ezcsp__eq", FOR_ANY_SOLVER, false },

		{ (char *)"#\\=", (char *)"ezcsp__neq", FOR_ANY_SOLVER, false },

		{ (char *)"#=>", (char *)"ezcsp__impl_r", FOR_ANY_SOLVER, false },
		{ (char *)"#<=", (char *)"ezcsp__impl_l", FOR_SICSTUS, false },
		{ (char *)"#=>", (char *)"ezcsp__impl_l", FOR_BPROLOG|INVERT_ARGS, false },

		{ (char *)"#\\/", (char *)"ezcsp__or", FOR_ANY_SOLVER, false },
		{ (char *)"#/\\", (char *)"ezcsp__and", FOR_ANY_SOLVER, false },
		{ (char *)"#\\", (char *)"ezcsp__xor", FOR_ANY_SOLVER, false },
		{ (char *)"#<=>", (char *)"ezcsp__diff", FOR_ANY_SOLVER, false },
		{ (char *)"#\\", (char *)"ezcsp__not", FOR_ANY_SOLVER, false },

		{ (char *)"assert_clause", (char *)"ezcsp__prolog_if", FOR_ANY_SOLVER, false },
		{ (char *)"prolog_query", (char *)"ezcsp__prolog_query", FOR_ANY_SOLVER, false },

		{ (char *)"+", (char *)"ezcsp__pl", FOR_ANY_SOLVER, false },
		{ (char *)"-", (char *)"ezcsp__mn", FOR_ANY_SOLVER, false },
		{ (char *)"*", (char *)"ezcsp__tm", FOR_ANY_SOLVER, false },
		{ (char *)"/", (char *)"ezcsp__dv", FOR_ANY_SOLVER, false },
		{ (char *)"mod", (char *)"ezcsp__mod", FOR_ANY_SOLVER, false },
		{ (char *)"//", (char *)"ezcsp__div", FOR_ANY_SOLVER, false },
		{ (char *)"max", (char *)"ezcsp__max", FOR_ANY_SOLVER, false },
		{ (char *)"min", (char *)"ezcsp__min", FOR_ANY_SOLVER, false },
		{ (char *)"abs", (char *)"ezcsp__abs", FOR_ANY_SOLVER, false },
		{ (char *)"pow", (char *)"ezcsp__pow", FOR_ANY_SOLVER, false },
		{ (char *)"exp", (char *)"ezcsp__exp", FOR_ANY_SOLVER, false },
		{ (char *)"**", (char *)"ezcsp__starstar", FOR_ANY_SOLVER, false },
		{ (char *)"sin", (char *)"ezcsp__sin", FOR_ANY_SOLVER, false },
		{ (char *)"cos", (char *)"ezcsp__cos", FOR_ANY_SOLVER, false },
		{ (char *)"tan", (char *)"ezcsp__tan", FOR_ANY_SOLVER, false },

		{ (char *)"sum_bp", (char *)"ezcsp__sum", FOR_BPROLOG, false },	/* sum(L,Rel,Var) is not defined in B-Prolog 8.1, so we need to use a replacement */
		{ (char *)"sum", (char *)"ezcsp__sum", FOR_ANY_SOLVER, false },

		{ (char *)"sics4_cumulative", (char *)"cumulative", FOR_SICSTUS4, false },

		{ (char *)"bp_cumulative", (char *)"cumulative", FOR_BPROLOG, false },
		{ (char *)"bp_disjoint2", (char *)"disjoint2", FOR_BPROLOG, false },

		{ NULL, NULL}
	},
	map_qr[]=
	{	{ (char *)">", (char *)"ezcsp__gt", FOR_ANY_SOLVER, false },

		{ (char *)">=", (char *)"ezcsp__geq", FOR_ANY_SOLVER, false },

		{ (char *)"<", (char *)"ezcsp__lt", FOR_ANY_SOLVER, false },

		{ (char *)"=<", (char *)"ezcsp__leq", FOR_ANY_SOLVER, false },

		{ (char *)"=", (char *)"ezcsp__eq", FOR_ANY_SOLVER, false },

		{ (char *)"=\\=", (char *)"ezcsp__neq", FOR_SWIPROLOG, false },	/* inequality in SWI-Prolog */
		{ (char *)"\\=", (char *)"ezcsp__neq", FOR_ANY_SOLVER, false }, /* default symbol for inequality */

		{ (char *)"+", (char *)"ezcsp__pl", FOR_ANY_SOLVER, false },
		{ (char *)"-", (char *)"ezcsp__mn", FOR_ANY_SOLVER, false },
		{ (char *)"*", (char *)"ezcsp__tm", FOR_ANY_SOLVER, false },
		{ (char *)"/", (char *)"ezcsp__dv", FOR_ANY_SOLVER, false },
		{ (char *)"**", (char *)"ezcsp__starstar", FOR_ANY_SOLVER, false },
		{ (char *)"//", (char *)"ezcsp__div", FOR_ANY_SOLVER, false },
		{ (char *)"mod", (char *)"ezcsp__mod", FOR_ANY_SOLVER, false },
		{ (char *)"max", (char *)"ezcsp__max", FOR_ANY_SOLVER, false },
		{ (char *)"min", (char *)"ezcsp__min", FOR_ANY_SOLVER, false },
		{ (char *)"abs", (char *)"ezcsp__abs", FOR_ANY_SOLVER, false },
		{ (char *)"pow", (char *)"ezcsp__pow", FOR_ANY_SOLVER, false },
		{ (char *)"exp", (char *)"ezcsp__exp", FOR_ANY_SOLVER, false },
		{ (char *)"sin", (char *)"ezcsp__sin", FOR_ANY_SOLVER, false },
		{ (char *)"cos", (char *)"ezcsp__cos", FOR_ANY_SOLVER, false },
		{ (char *)"tan", (char *)"ezcsp__tan", FOR_ANY_SOLVER, false },

		{ (char *)"sum", (char *)"ezcsp__sum", FOR_ANY_SOLVER, false },

		{ NULL, NULL}
	},
	map_lp[]=
	{	{ (char *)"$>=", (char *)"ezcsp__geq", FOR_ANY_SOLVER, false },

		{ (char *)"$=<", (char *)"ezcsp__leq", FOR_ANY_SOLVER, false },

		{ (char *)"$=", (char *)"ezcsp__eq", FOR_ANY_SOLVER, false },

		{ (char *)"+", (char *)"ezcsp__pl", FOR_ANY_SOLVER, false },
		{ (char *)"-", (char *)"ezcsp__mn", FOR_ANY_SOLVER, false },
		{ (char *)"*", (char *)"ezcsp__tm", FOR_ANY_SOLVER, false },
		{ (char *)"/", (char *)"ezcsp__dv", FOR_ANY_SOLVER, false },
		{ (char *)"**", (char *)"ezcsp__starstar", FOR_ANY_SOLVER, false },
		{ (char *)"//", (char *)"ezcsp__div", FOR_ANY_SOLVER, false },

		{ (char *)"max", (char *)"ezcsp__max", FOR_ANY_SOLVER, false },
		{ (char *)"min", (char *)"ezcsp__min", FOR_ANY_SOLVER, false },

		{ (char *)"sum", (char *)"ezcsp__sum", FOR_ANY_SOLVER, false },

		{ NULL, NULL}
	},
	map_gams[]=
	{	{ (char *)"=g=", (char *)"ezcsp__geq", FOR_GAMS, true },

		{ (char *)"=l=", (char *)"ezcsp__leq", FOR_GAMS, true },

		{ (char *)"=e=", (char *)"ezcsp__eq", FOR_GAMS, true },

		{ (char *)"+", (char *)"ezcsp__pl", FOR_GAMS, true },
		{ (char *)"-", (char *)"ezcsp__mn", FOR_GAMS, true },
		{ (char *)"*", (char *)"ezcsp__tm", FOR_GAMS, true },
		{ (char *)"/", (char *)"ezcsp__dv", FOR_GAMS, true },
		{ (char *)"**", (char *)"ezcsp__starstar", FOR_GAMS, true },
		{ (char *)"//", (char *)"ezcsp__div", FOR_GAMS, true },

		{ (char *)"max", (char *)"ezcsp__max", FOR_GAMS, true },
		{ (char *)"min", (char *)"ezcsp__min", FOR_GAMS, true },

		{ (char *)"abs", (char *)"ezcsp__abs", FOR_GAMS, false },
		{ (char *)"pow", (char *)"ezcsp__pow", FOR_GAMS, false },
		{ (char *)"exp", (char *)"ezcsp__exp", FOR_GAMS, false },
		{ (char *)"sin", (char *)"ezcsp__sin", FOR_GAMS, false },
		{ (char *)"cos", (char *)"ezcsp__cos", FOR_GAMS, false },
		{ (char *)"tan", (char *)"ezcsp__tan", FOR_GAMS, false },

		/*
		 * Functors that must be expanded later.
		 * Syntax: !!<op>:<neutral element>
		 */
		{ (char *)"!!+:0", (char *)"ezcsp__sum", FOR_GAMS, false },

		{ NULL, NULL}
	}, *map;

	int solver_mask;

	solver_mask=1<<cpsolver_type;

	if (cpsolver_type==CPSOLVER_GAMS)
		/* GAMS uses the same (non-Prolog) syntax for every domain */
		map=map_gams;
	else
	if (cpsolver_type==CPSOLVER_MINIZINC)
		/* MZN syntax mapping */
		map=map_mzn;
	else if (cpsolver_type==CPSOLVER_GUROBI)
		/* Gurobi syntax mapping */
		map=map_gurobi;
	else
	if (csp->domain=="fd")
		map=map_fd;
	else
	if (csp->domain=="lp")
		map=map_lp;
	else
		map=map_qr;
//fprintf(stderr,"got it! %s\n",a->relation);

	for(i=0;map[i].from!=NULL;i++)
	{	if (strcmp(a->relation,map[i].from)==0 &&
		    (map[i].which_solvers==FOR_ANY_SOLVER ||
		     (map[i].which_solvers & solver_mask)
		    ))
		{	
//fprintf(stderr,"match! %s\n",a->relation);

			free(a->relation);

			a->relation=strdup(map[i].to);
			a->is_infix=map[i].infix;

			if (map[i].which_solvers & UNSUPPORTED)
			{	fprintf(stderr,"***%s: %s is not supported by the CP solver selected.\n",(allow_unsupported) ? "WARNING":"ERROR",a->relation);
				if (!allow_unsupported) exit(1);
			}

			if ((map[i].which_solvers & INVERT_ARGS) && a->arity>0)
			{	struct item **args;
				args=(struct item **)calloc((int)a->arity,sizeof(struct item *));

				for(i=0;i<a->arity;i++)
					args[i]=a->args[a->arity-i-1];
				free(a->args);
				a->args=args;
			}

			break;
		}
	}

	for(i=0;i<a->arity;i++)
		fix_item(a->args[i],csp,cpsolver_type,allow_unsupported);
}

void fix_syntax(struct rule *r,CSP *csp,int cpsolver_type, bool allow_unsupported)
{	int i;

	if (r->type==RULE_SYSTEM_DIRECTIVE) return;	// nothing to be done

	for(i=0;i<r->head_size;i++)
	{	if (strcmp(r->head[i]->relation,"required")==0 && (r->head[i]->arity==1))
			fix_item(r->head[i]->args[0],csp,cpsolver_type,allow_unsupported);
		else
		/* the only thing we need to do for label_option is renaming min/max to ezcsp__min/max */
		if (strcmp(r->head[i]->relation,"label_option")==0 && (r->head[i]->arity==1))
			fix_item(r->head[i]->args[0],csp,cpsolver_type,allow_unsupported);
		else
		/* the only thing we need to do for lpobjective is renaming min/max to ezcsp__min/max */
		if (strcmp(r->head[i]->relation,"lpobjective")==0 && (r->head[i]->arity==1))
			fix_item(r->head[i]->args[0],csp,cpsolver_type,allow_unsupported);
	}

	/* the body is guaranteed to be empty because we are processing an answer set */
}

void output_cspdomain(CSP *csp,FILE *fpo,int cpsolver_type)
{	struct
	{	char *domain,*lib;
	}
	domains[]=
	{	{ (char *)"fd", (char *)"clpfd" },
		{ (char *)"q", (char *)"clpq" },
		{ (char *)"r", (char *)"clpr" },
		{ NULL, NULL }
	};

	int i;

	if (cpsolver_type==CPSOLVER_BPROLOG)
		return;	// BProlog does not need library statements

	fputs(":- use_module(library(lists)).\n",fpo);

	for(i=0;domains[i].domain!=NULL;i++)
	{	if (csp->domain==domains[i].domain)
			break;
	}
	if (domains[i].domain==NULL)
	{	clog << "ERROR: unknown csp domain " << csp->domain << endl;
		exit(1);
	}
	
	fprintf(fpo,":- use_module(library(%s)).\n",domains[i].lib);

	fputs(charsio_lib[cpsolver_type],fpo);
	fprintf(fpo,"\n");

	fprintf(fpo,"\n");
}

/*
 * Create the subtree for a-args[0] op a-args[1] ... op a-args[n]
 * ASSUMPTION: arg a is a [] list.
 * ASSUMPTION: a->args contains at least one element.
 * POST-CONDITION: every pointer in a->args is NULL.
 */
struct item *interleave_operator(struct item *a, char *op, char *neutral_elem, int start)
{	if (a->arity==0)
	{	/* empty list: replace with the neutral element */
		struct item *subt=maketerm(0);
		subt->relation=strdup(neutral_elem);
		return(subt);
	}
	
	if (start==a->arity-1)
	{	/* last element */
		struct item *arg=a->args[start];
		a->args[start]=NULL;
		return(arg);
	}

	struct item *subt=maketerm(2);
	subt->relation=strdup(op);
	subt->is_infix=1;
	subt->args[0]=a->args[start];
	subt->args[1]=interleave_operator(a,op,neutral_elem,start+1);
	a->args[start]=NULL;
	return(subt);
}

void expand_functor(struct item *a)
{	if (strncmp(a->relation,"!!",2)==0 &&
	    a->arity==3 &&
	    strcmp(a->args[0]->relation,"[")==0)
	{	struct item *subt;
		int i;

		for(i=2;a->relation[i]!=0 && a->relation[i]!=':';i++);
		if (a->relation[i]==0)
		{	fprintf(stderr,"***INTERNAL ERROR: expandable functor in fix_item() has incorrect syntax specification.\n");
			exit(1);
		}
		a->relation[i]=0;
		subt=interleave_operator(a->args[0],&a->relation[2],&a->relation[i+1],0);
		free(a->args[0]->args);
		free(a->args[0]->relation);
		free(a->args[0]);
		a->args[0]=subt;
		free(a->relation);
		a->relation=strdup(a->args[1]->relation);
		a->is_infix=true;
		a->arity=2;
		a->args[1]=a->args[2];
		a->args[2]=NULL;
	}
	else
		for(int i=0;i<a->arity;i++)
			expand_functor(a->args[i]);
}

bool replace_ezcsp_list_pattern_vars(CSP *csp,struct item *v,vector<int> &vars)
{	char str[100];
	vector<int> vars2;

/*	for(int j=0;j<(int)csp->labeling.size();j++)
	{	idx=j+1;
		if (item_matches_pattern(csp,csp->labeling[j],v))
			vars2.push_back(idx);
	}
*/	for(int j=0;j<(int)csp->cspvar.size();j++)
	{	if (item_matches_pattern(csp,csp->cspvar[j]->args[0],v))
			vars2.push_back(get_var_index(csp,csp->cspvar[j]->args[0]));
	}
	if (vars2.size()==0) return(false);

	v->relation=strdup("[");
	v->is_infix=0;
	v->is_parenthesis=1;
	v->arglist_end=']';
	v->args=(struct item **)calloc((int)vars2.size(),sizeof(struct item *));
	v->arity=(int)vars2.size();
	for(int j=0;j<(int)vars2.size();j++)
	{	v->args[j]=(struct item *)calloc(1,sizeof(struct item));
		sprintf(str,"X%d",vars2[j]);
		v->args[j]->relation=strdup(str);
		v->args[j]->arity=0;
		vars.push_back(vars2[j]);
	}

	return(true);
}

bool replace_ezcsp_list_pattern_rel(CSP *csp,struct item *v,vector<int> &vars)
{	vector<int> rels;

	for(int j=0;j<(int)csp->sorted_facts.size();j++)
	{	if (item_matches_pattern(csp,csp->sorted_facts[j],v))
			rels.push_back(j);
	}
	if (rels.size()==0) return(false);
			
	v->relation=strdup("[");
	v->is_infix=0;
	v->is_parenthesis=1;
	v->arglist_end=']';
	v->args=(struct item **)calloc((int)rels.size(),sizeof(struct item *));
	v->arity=(int)rels.size();
	for(int j=0;j<(int)rels.size();j++)
	{	struct item *atom,*x;
		int idx;
	
		atom=csp->sorted_facts[rels[j]];
		x=atom->args[atom->arity-1];	// get the last arg
		idx=get_var_index(csp,x);
		if (idx!=0)
		{	char str[100];

			v->args[j]=(struct item *)calloc(1,sizeof(struct item));
			sprintf(str,"X%d",idx);
			v->args[j]->relation=strdup(str);
			v->args[j]->arity=0;
			vars.push_back(idx);
		}
		else
			v->args[j]=x;
	}
	
	return(true);
}

void replace_ezcsp_list_pattern(CSP *csp,struct item *v,vector<int> &vars)
{	if (replace_ezcsp_list_pattern_vars(csp,v,vars))
		return;
	if (!replace_ezcsp_list_pattern_rel(csp,v,vars))
	{	v->relation=strdup("[");
		v->is_infix=0;
		v->is_parenthesis=1;
		v->arglist_end=']';
		v->arity=0;
	}
}

void replace_ezcsp_extlist(CSP *csp,struct item *v,vector<int> &vars)
{	vector<int> vars2;

	if (strcmp(v->relation,"extlist")!=0)
		return;

	v->relation=strdup("[");
	v->is_infix=0;
	v->is_parenthesis=1;
	v->arglist_end=']';
	for(int j=0;j<(int)v->arity;j++)
	{	int idx;
	
		idx=get_var_index(csp,v->args[j]);
		if (idx!=0)
		{	char str[100];

			v->args[j]=(struct item *)calloc(1,sizeof(struct item));
			sprintf(str,"X%d",idx);
			v->args[j]->relation=strdup(str);
			v->args[j]->arity=0;
			vars.push_back(idx);
		}
		else
		{
			for(int k=0;k<(int)csp->sorted_facts.size();k++)
			{	if (sameItem(csp->sorted_facts[k],v->args[j]))
				{	struct item *atom;

					atom=csp->sorted_facts[k];

					v->args[j]=atom->args[atom->arity-1];	// get the last arg
				}
			}
		}
	}
}

vector<int> replace_ezcsp_vars(CSP *csp,struct item *v)
{	vector<int> vars;

	for(int i=0;i<v->arity;i++)
	{	int idx;

		if (strcmp(v->relation,"list")==0 && v->arity==2)
		{	replace_ezcsp_list_pattern(csp,v,vars);

			continue;
		}

		if (strcmp(v->relation,"extlist")==0)
		{	replace_ezcsp_extlist(csp,v,vars);

			continue;
		}

		idx=get_var_index(csp,v->args[i]);
		if (idx!=0)
		{	char str[100];
		
			sprintf(str,"X%d",idx);
			v->args[i]->relation=strdup(str);
			v->args[i]->arity=0;
			vars.push_back(idx);
		}
		else
		{	vector<int> vars2;
		
			vars2=replace_ezcsp_vars(csp,v->args[i]);
			for(int j=0;j<(int)vars2.size();j++)
				vars.push_back(vars2[j]);
		}
	}

	return(vars);
}

void output_csp_constraint(CSP *csp,int i,struct item *req,FILE *fpo,int cpsolver_type)
{	fprintf(fpo,"constr(%d, Q) :- \n",i);

	vector<int> vars;
	vars=replace_ezcsp_vars(csp,req);

	// nth
	for(int i=0;i<(int)vars.size();i++)
		fprintf(fpo,"\t%s(%d, Q, X%d),\n",nth_rel[cpsolver_type],vars[i],vars[i]);
	fprintf(fpo,"\t");
	// In R and Q domains, only surround the constraint in brackets if it is an arithmetic one
	if ((csp->domain=="r" || csp->domain=="q") && req->args[0]->relation[0]<'a')
		fprintf(fpo,"{ ");
	output_atom_to_file(req->args[0],fpo);
	// In R and Q domains, only surround the constraint in brackets if it is an arithmetic one
	if ((csp->domain=="r" || csp->domain=="q") && req->args[0]->relation[0]<'a')
		fprintf(fpo," }");
	fprintf(fpo,".\n");

	fprintf(fpo,"\n");
}

void output_csp_constraint_GAMS(CSP *csp,int i,struct item *req,FILE *fpo,int cpsolver_type)
{	fprintf(fpo,"r%d.. ",i);

	vector<int> vars;
	vars=replace_ezcsp_vars(csp,req);

	expand_functor(req);

	// nth
//	for(int i=0;i<(int)vars.size();i++)
//		fprintf(fpo,"\t%s(%d, Q, X%d),\n",nth_rel[cpsolver_type],vars[i],vars[i]);

	output_atom_to_file(req->args[0],fpo);
	fprintf(fpo," ;\n");

	//fprintf(fpo,"\n");
}

void output_lp_solve(CSP *csp,FILE *fpo,int cpsolver_type)
{	vector<int> vars;

	if (csp->objective!=NULL)
	{
		vars=replace_ezcsp_vars(csp,csp->objective);

		// nth
		for(int i=0;i<(int)vars.size();i++)
			fprintf(fpo,"\t%s(%d, Q, X%d),\n",nth_rel[cpsolver_type],vars[i],vars[i]);

		fprintf(fpo,"\tlp_solve(Q,");
		output_atom_to_file(csp->objective,fpo);
		fprintf(fpo,").\n");
	}
	else
		fprintf(fpo,"\tlp_solve(Q).\n");
}

void output_csp_GAMS(CSP *csp,FILE *fpo,int cpsolver_type)
{
	fprintf(fpo,"* Make output less verbose\n");
	fprintf(fpo,"$offlisting\n");
	fprintf(fpo,"$offsymxref offsymlist\n");
	fprintf(fpo,"option\n");
	fprintf(fpo,"\tlimrow = 0,\n");
	fprintf(fpo,"\tlimcol = 0,\n");
	fprintf(fpo,"\tsolprint = off,\n");
	fprintf(fpo,"\tsysout = off;\n");
	fprintf(fpo,"\n");


	/*
	 * NOTE: the encoding is created so that it has extra variable X0
	 *       and extra equation r0:
	 *         r0.. X0 =e= 0 ;
	 *
	 *       Variable X0 is the one on which the solution is minimized.
	 *       We use this trick to minimize the computation time given
	 *       that we don't care about optimization.
	 *
	 */

	// vars
	fprintf(fpo,"Variables X0");
	for(int i=0;i<(int)csp->cspvar.size();i++)
	{	struct item *v;

		v=csp->cspvar[i];
		int idx=get_var_index(csp,v->args[0]);
		if (idx==0)
		{	clog << "ERROR: unknown variable with term " << v->args[0]->relation << endl;
			exit(1);
		}
		fprintf(fpo,", X%d",idx);
	}
	fprintf(fpo,";\n");

	// constr
	fprintf(fpo,"Equations r0");
	for(int i=0;i<(int)csp->required.size();i++)
		fprintf(fpo,", r%d",i+1);
	for(int i=0;i<(int)csp->cspvar.size();i++)
	{	struct item *v;

		v=csp->cspvar[i];
		if (v->arity==3)
			fprintf(fpo,", r%d_l, r%d_u",(int)csp->required.size()+i+1,(int)csp->required.size()+i+1);
	}
	fprintf(fpo,";\n");

	// output the hardcoded equation "r0.. X0 =e= 0 ;"
	// which is used to prevent the solver from optimizing
	// the solutions
	fprintf(fpo,"* hardcoded equation to only solve decision problems\n");
	fprintf(fpo,"r0.. X0 =e= 0 ;\n");

	// constr
	for(int i=0;i<(int)csp->required.size();i++)
	{	fprintf(fpo,"* ");
		output_atom_to_file(csp->required[i],fpo);
		fprintf(fpo,"\n");
		output_csp_constraint_GAMS(csp,i+1,csp->required[i],fpo,cpsolver_type);
	}
	for(int i=0;i<(int)csp->cspvar.size();i++)
	{	struct item *v;

		v=csp->cspvar[i];
		if (v->arity==3)
		{	int idx=get_var_index(csp,v->args[0]);
			fprintf(fpo,"r%d_l.. X%d =g= %s ;\n",(int)csp->required.size()+i+1,idx,v->args[1]->relation);
			fprintf(fpo,"r%d_u.. X%d =l= %s ;\n",(int)csp->required.size()+i+1,idx,v->args[2]->relation);
		}
	}
	fprintf(fpo,"\n");

	fprintf(fpo,"Model cpmodel / ALL / ;\n");
	fprintf(fpo,"Solve cpmodel using %s ",csp->domain.c_str());
	if (csp->domain!="mcp" && csp->domain!="cns")
		/* MCP and CNS do not involve any optimimzation process */
		fprintf(fpo,"minimizing X0 ");
	fprintf(fpo,";\n");

	// output value assignments to the .lst file
	fprintf(fpo,"file output/ '' / ;\n");
	fprintf(fpo,"put output;\n");
	fprintf(fpo,"if(cpmodel.Modelstat gt %%ModelStat.Locally Optimal%%,\n");
	fprintf(fpo,"    put '++failed' / ;\n");
	fprintf(fpo,"else\n");
	fprintf(fpo,"    put '++succeeded' / ;\n");
	for(int i=0;i<(int)csp->labeling.size();i++)
	{	fprintf(fpo,"$if defined X%d put '++",i+1);
		output_atom_to_file(csp->labeling[i],fpo);
		fprintf(fpo,"=' X%d.l:<:8 / ;\n",i+1);
	}
	fprintf(fpo,");\n");
	fprintf(fpo,"putclose output ;\n");

}

void output_csp(CSP *csp,FILE *fpo,int cpsolver_type,bool relaxed_labeling)
{
	if (cpsolver_type==CPSOLVER_GAMS)
	{	output_csp_GAMS(csp,fpo,cpsolver_type);
		return;
	}

	if (cpsolver_type==CPSOLVER_MINIZINC)
	{	output_csp_MZN(csp,fpo,cpsolver_type);
		return;
	}

	if (cpsolver_type==CPSOLVER_GUROBI)
	{	output_csp_GUROBI(csp,fpo,cpsolver_type);
		return;
	}

	output_cspdomain(csp,fpo,cpsolver_type);

	fputs(which_solver[cpsolver_type],fpo);
	fprintf(fpo,"\n");

	fprintf(fpo,"solve(A) :-\n");
	fprintf(fpo,"\tlength(Q, %d),\n",(int)csp->labeling.size());
	for(int i=0;i<(int)csp->cspvar.size();i++)
	{	struct item *v;
	
		v=csp->cspvar[i];
		int idx=get_var_index(csp,v->args[0]);
		if (idx==0)
		{	clog << "ERROR: unknown variable with term " << v->args[0]->relation << endl;
			exit(1);
		}

		if (v->arity==3)
		{	fprintf(fpo,"\tdom(%d, Q, %s, %s),",idx,v->args[1]->relation,v->args[2]->relation);
			fprintf(fpo,"   %% ");
		}
		else
			fprintf(fpo,"\t%% ");
		output_atom_to_file(v,fpo);
		fprintf(fpo,"\n");
	}

	if (csp->domain=="lp")
	{	for(int i=0;i<(int)csp->lpinteger.size();i++)
		{	struct item *v;
	
			v=csp->lpinteger[i];
			int idx=get_var_index(csp,v->args[0]);
			if (idx==0)
			{	clog << "ERROR: unknown variable with term " << v->args[0]->relation << endl;
				exit(1);
			}

			fprintf(fpo,"\tlpint(%d, Q),",idx);
			fprintf(fpo,"   %% ");
			output_atom_to_file(v,fpo);
			fprintf(fpo,"\n");
		}
	}

	bool domain_fd=(csp->domain=="fd");
	int max_output_queries=(domain_fd) ? 1:0;
	// constr
	for(int output_queries=0;output_queries<=max_output_queries;output_queries++)
	{	for(int i=0;i<(int)csp->required.size();i++)
		{	int is_query=(domain_fd) && (strcmp(csp->required[i]->args[0]->relation,"prolog_query")==0);

			if (output_queries == is_query)
			{	fprintf(fpo,"\tconstr(%d, Q),",i+1);
				fprintf(fpo,"   %% ");
				output_atom_to_file(csp->required[i],fpo);
				fprintf(fpo,"\n");
			}
		}
	}

	if (csp->domain=="lp")
		fprintf(fpo,"\tlpslv(Q),\n");
	else
	if ((csp->domain=="r" || csp->domain=="q") && !relaxed_labeling)
		fprintf(fpo,"\tlabeling_sim(Q),\n");
	else
	if (csp->domain=="fd")
	{	// labeling
		fprintf(fpo,"\tlabeling([");
		string sep="";
		for(int i=0;i<(int)csp->label_options.size();i++)
		{	fprintf(fpo,"%s%s",sep.c_str(),csp->label_options[i].c_str());
			sep=", ";
		}
		fprintf(fpo,"], Q),\n");
	}

	// form_result
	fprintf(fpo,"\tform_result(Q, A).\n");
/*
	fprintf(fpo,"\tform_result(Q, [");
	sep="";
	for(int i=0;i<(int)csp->labeling.size();i++)
	{	fprintf(fpo,"%s",sep.c_str());
		output_atom_to_file(csp->labeling[i],fpo);
		sep=", ";
	}
	fprintf(fpo,"], A).\n");
*/
	fprintf(fpo,"\n");


	fprintf(fpo,"dom(A, B, C, D) :-\n");
	fprintf(fpo,"\t%s(A, B, E),\n",nth_rel[cpsolver_type]);
	if (csp->domain=="lp")
		fprintf(fpo,"\tlp_domain(E, C, D).\n");
	if (csp->domain=="fd")
	{	if (cpsolver_type==CPSOLVER_SWIPROLOG)
			fprintf(fpo,"\tE in C..D.\n");
		else
			fprintf(fpo,"\tdomain([E], C, D).\n");
	}
	else
		fprintf(fpo,"\t{ E >= C, E =< D }.\n");
	fprintf(fpo,"\n");

	if (csp->domain=="fd" && cpsolver_type==CPSOLVER_BPROLOG)
	{	/* Workaround suggested by Neng-Fa [03/09/2017]
		 * for bug in BProlog 7.5+ that breaks #\/.
		 */
		fprintf(fpo,"'$bc_clause1'(V1) => V1=1.\n\n");
		/* Implementation of sum/3 for FD domain in B-Prolog 
		 * due to the fact that sum/3 is not defined in B-Prolog 8.1 
		 */
		fprintf(fpo,"sum_bp(List,Op,Var) :-\n");
		fprintf(fpo,"\tC =.. [Op,sum(List),Var],\n");
		fprintf(fpo,"\tC.\n\n");
	}

	if (csp->domain=="lp")
	{	fprintf(fpo,"lpint(A, B) :-\n");
		fprintf(fpo,"\t%s(A, B, E),\n",nth_rel[cpsolver_type]);
		fprintf(fpo,"\tlp_integer(E).\n");
		fprintf(fpo,"\n\n");

		/* Implementation of sum/3 for LP domain when Op is = */
//		fprintf(fpo,"sum(List,$=,Var) :-\n");
//		fprintf(fpo,"\tsum(List) $= Var.\n");
		fprintf(fpo,"sum(List,Op,Var) :-\n");
		fprintf(fpo,"\tC =.. [Op,sum(List),Var],\n");
		fprintf(fpo,"\tC.\n\n");
	}

	// vname
	for(int i=0;i<(int)csp->labeling.size();i++)
	{	fprintf(fpo,"vname(%d,",i+1);
		output_atom_to_file(csp->labeling[i],fpo);
		fprintf(fpo,").\n");
	}

	// constr
	for(int i=0;i<(int)csp->required.size();i++)
	{	fprintf(fpo,"%% ");
		output_atom_to_file(csp->required[i],fpo);
		fprintf(fpo,"\n");
		output_csp_constraint(csp,i+1,csp->required[i],fpo,cpsolver_type);
	}
	fprintf(fpo,"\n");


	fprintf(fpo,"to_comma_list([E],E).\n");
	fprintf(fpo,"to_comma_list([E|T],(E,L)) :-\n");
	fprintf(fpo,"\tto_comma_list(T,L).\n");
	fprintf(fpo,"\n");

	fprintf(fpo,"assert_clause(Head,Body) :-\n");
	fprintf(fpo,"\tto_comma_list(Body,List),\n");
	fprintf(fpo,"\tassert((Head :- List)).\n");
	fprintf(fpo,"\n");

	fprintf(fpo,"prolog_query(X) :-\n");
	fprintf(fpo,"\tX.\n");
	fprintf(fpo,"\n");


	if (csp->domain=="lp")
	{	// lp_solve call
		fprintf(fpo,"lpslv(Q) :- \n");
		output_lp_solve(csp,fpo,cpsolver_type);
		fprintf(fpo,"\n");
	}
	fprintf(fpo,"\n");

	/* output the <PL_RELATION_PREFIX>XXX facts, which are input to the defined part */
	for(int i=0;i<(int)csp->sorted_facts.size();i++)
	{	/*
		 * Do not output strongly-negated literals, because
		 * they are typically not supported by Prolog interpreters.
		 */
		if (!csp->sorted_facts[i]->strong_negation && startsWith(csp->sorted_facts[i]->relation,PL_RELATION_PREFIX))
		{	output_atom_to_file(csp->sorted_facts[i],fpo);
			fprintf(fpo,".\n");
		}
	}
	fprintf(fpo,"\n");


/*
	fprintf(fpo,"form_result([],[],[]).\n");
	fprintf(fpo,"form_result([V|VarsTail],[Name|NTail],[(Name,V)|MTail]) :- \n");
	fprintf(fpo,"\tform_result(VarsTail,NTail,MTail).\n");
	fprintf(fpo,"\n");
*/

	fprintf(fpo,"form_result(Q,A) :-\n");
	if (csp->domain=="r" || csp->domain=="q")
	{	fprintf(fpo,"\tform_result(Q, 1, Avar),\n");
		fprintf(fpo,"\tform_final_mapping(Q, Avar, A).\n");
		fprintf(fpo,"\n");
		fprintf(fpo,"form_final_mapping(Q,Mapping,FinalMapping) :-\n");
		fprintf(fpo,"\tremove_value_assigned(Q,Q2),\n");
		fprintf(fpo,"\tvalue_assigned_mapping(Mapping,VMapping),\n");
		fprintf(fpo,"\tform_final_mapping2(Q2,Mapping,RQMapping),\n");
		fprintf(fpo,"\tappend(VMapping,RQMapping,FinalMapping).\n");
		fprintf(fpo,"\n");		
		fprintf(fpo,"remove_value_assigned([],[]).\n");
		fprintf(fpo,"remove_value_assigned([V|Q],[V|Q2]) :-\n");
		fprintf(fpo,"\tvar(V),\n");
		fprintf(fpo,"\t!,\n");
		fprintf(fpo,"\tremove_value_assigned(Q,Q2).\n");
		fprintf(fpo,"remove_value_assigned([_|Q],Q2) :-\n");
		fprintf(fpo,"\tremove_value_assigned(Q,Q2).\n");
		fprintf(fpo,"\n");
		fprintf(fpo,"value_assigned_mapping([],[]).\n");
		fprintf(fpo,"value_assigned_mapping([(ASPName,V)|Mapping],[(ASPName,V)|VMapping]) :-\n");
		fprintf(fpo,"\t\\+ var(V),\n");
		fprintf(fpo,"\t!,\n");
		fprintf(fpo,"\tvalue_assigned_mapping(Mapping,VMapping).\n");
		fprintf(fpo,"value_assigned_mapping([_|Mapping],VMapping) :-\n");
		fprintf(fpo,"\tvalue_assigned_mapping(Mapping,VMapping).\n");
		fprintf(fpo,"\n");
		fprintf(fpo,"form_final_mapping2(Q, Mapping, A) :-\n");
		fprintf(fpo,"\tdump(Q,V,C),\n");
		fprintf(fpo,"\trename_termlist(C,A,Q,V,Mapping).\n");
		fprintf(fpo,"\n");
		fprintf(fpo,"rename_termlist([Arg|Args],[RenArg|RenArgs],Q,V,Mapping) :-\n");
		fprintf(fpo,"\trename_term(Arg,RenArg,Q,V,Mapping),\n");
		fprintf(fpo,"\trename_termlist(Args,RenArgs,Q,V,Mapping).\n");
		fprintf(fpo,"\n");
		fprintf(fpo,"rename_termlist([],[],_,_,_).\n");
		fprintf(fpo,"\n");
		fprintf(fpo,"rename_term(C,A,Q,V,Mapping) :-\n");
		fprintf(fpo,"\tvar(C),\n");
		fprintf(fpo,"\t!,\n");
		fprintf(fpo,"\tmap_varsrq(C,A,Q,V,Mapping).\n");
		fprintf(fpo,"\n");
		fprintf(fpo,"rename_term(C,C,Q,V,Mapping) :-\n");
		fprintf(fpo,"\t\\+ compound(C), !.\n");
		fprintf(fpo,"\n");
		fprintf(fpo,"rename_term([],[],Q,V,Mapping) :-\n");
		fprintf(fpo,"\t!.\n");
		fprintf(fpo,"\n");
		fprintf(fpo,"rename_term(C,A,Q,V,Mapping) :-\n");
		fprintf(fpo,"\tC =.. [FC|Args],\n");
		fprintf(fpo,"\tmap_varsrq(FC,FA,Q,V,Mapping),\n");
		fprintf(fpo,"\trename_termlist(Args,RenArgs,Q,V,Mapping),\n");
		fprintf(fpo,"\tA =.. [FA|RenArgs].\n");
		fprintf(fpo,"\n");
		fprintf(fpo,"map_varsrq(C,C,_,_,_) :-\n");
		fprintf(fpo,"\t\\+ var(C).\n");
		fprintf(fpo,"\n");
		fprintf(fpo,"map_varsrq(C,A,Q,V,[(A,Var)|_]) :-\n");
		fprintf(fpo,"\tvar(C),\n");
		fprintf(fpo,"\tvar_nth(N,V,C),\n");
		fprintf(fpo,"\t%s(N,Q,C2),\n",nth_rel[cpsolver_type]);
//		fprintf(fpo,"\t%s(N,V,C),\n",nth_rel[cpsolver_type]);
//		fprintf(fpo,"\t%s(N,Q,C2),\n",nth_rel[cpsolver_type]);
		fprintf(fpo,"\tvar_is_same(C2,Var),\n");
		fprintf(fpo,"\t!.\n");
		fprintf(fpo,"\n");
		fprintf(fpo,"var_is_same(VA,VB) :-\n");
		fprintf(fpo,"\t%s(VA,AnonymChars),\n",write_to_chars_rel[cpsolver_type]);
		fprintf(fpo,"\t%s(VB,AnonymChars).\n",write_to_chars_rel[cpsolver_type]);
		fprintf(fpo,"\n");
		fprintf(fpo,"swipl_write_to_chars(A,B) :-\n");
		fprintf(fpo,"\tformat(codes(B), '~w', [A]).\n");
		fprintf(fpo,"map_varsrq(C,A,Q,V,[_|Mapping]) :-\n");
		fprintf(fpo,"\tvar(C),\n");
		fprintf(fpo,"\tmap_varsrq(C,A,Q,V,Mapping).\n");
		fprintf(fpo,"\n");
		fprintf(fpo,"map_varsrq(C,C,_,_,[]).\n");
		fprintf(fpo,"\n");
		fprintf(fpo,"var_nth(N,List,Var) :-\n");
		fprintf(fpo,"\tvar_nth(1,N,List,Var).\n");
		fprintf(fpo,"var_nth(N,N,[V|_],Var) :-\n");
		fprintf(fpo,"\tvar_is_same(V,Var).\n");
		fprintf(fpo,"var_nth(N1,N,[_|Tail],Var) :-\n");
		fprintf(fpo,"\tN2 is N1+1,\n");
		fprintf(fpo,"\tvar_nth(N2,N,Tail,Var).\n");
		/* Try to assign actual values. Sound but incomplete. */
		fprintf(fpo,"labeling_sim([]).\n");
		fprintf(fpo,"labeling_sim([X|Tail]) :-\n");
		fprintf(fpo,"\tinf(X,Inf),\n");
		fprintf(fpo,"\t{ X = Inf },\n");
		fprintf(fpo,"\tlabeling_sim(Tail).\n");
		/* Implementation of sum/3 for R and Q domains. */
//		fprintf(fpo,"sum(List,=,Num) :-\n");
//		fprintf(fpo,"\tsum_of(List,Sum),\n");
//		fprintf(fpo,"\t{ Sum = Num }.\n");
		fprintf(fpo,"sum(List,Op,Num) :-\n");
		fprintf(fpo,"\tsum_of(List,Sum),\n");
		fprintf(fpo,"\tC =.. [Op,Sum,Num],\n");
		fprintf(fpo,"\t{ C }.\n");
		fprintf(fpo,"sum_of([],0).\n");
		fprintf(fpo,"sum_of([X | Tail],Sum) :-\n");
		fprintf(fpo,"\tsum_of(Tail,PartSum),\n");
		fprintf(fpo,"\t{ Sum = X + PartSum }.\n");
		fprintf(fpo,"\n");
	}
	else
		fprintf(fpo,"\tform_result(Q, 1, A).\n");

	fprintf(fpo,"form_result([],_,[]).\n");
	fprintf(fpo,"form_result([V|VarsTail],N,[(Name,V)|MTail]) :- \n");
	fprintf(fpo,"\tvname(N,Name),\n");
	fprintf(fpo,"\tnonvar(V),\n");
	fprintf(fpo,"\tN2 is N + 1,\n");
	fprintf(fpo,"\tform_result(VarsTail,N2,MTail).\n");
	fprintf(fpo,"form_result([V|VarsTail],N,[(Name,ezcspvarundef)|MTail]) :- \n");
	fprintf(fpo,"\tvname(N,Name),\n");
	fprintf(fpo,"\tvar(V),\n");
	fprintf(fpo,"\tN2 is N + 1,\n");
	fprintf(fpo,"\tform_result(VarsTail,N2,MTail).\n");
	fprintf(fpo,"\n");
}

#if 0
#include <stdio.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <stdlib.h>
vector<string> load_program2(int n_files,char* files[])
{
#define BUFS 102400
	char buf[BUFS+1];
	vector<string> p;

	for(int f=0;f<n_files;f++)
	{	int fd;
	
		if (strcmp(files[f],"--")==0)
			fd=fileno(stdin);
		else
		{	fd=open(files[f],O_RDONLY);
			if (fd==-1)
			{	std::clog << "Unable to read from file " << files[f] << "; skipping it." << std::endl;
				continue;
			}
		}
		
		int off,n;

		off=0;
		while ( ( n=read(fd, &buf[off], BUFS-off )) >  0)
		{	int i,st;
	
			n+=off;
			for(st=i=0;i<n;i++)
			{	if (buf[i]=='\n')
				{	buf[i]=0;
					p.push_back(&buf[st]);
					st=i+1;
				}
			}
			if (st<n)
			{	// Replacement for
				//	memcpy(buf,&buf[st],n-st)
				// that works for overlapping areas
				// and does not involve extra storage
				// like memmove().
				for(int j=0;j<n-st;j++)
					buf[j]=buf[j+st];
				off=n-st;
			}
			else
				off=0;
		}
		if (n<=0 && off>0)
		{	buf[off]=0;
			p.push_back(buf);
		}

		if (strcmp(files[f],"--")!=0)
			close(fd);
	}

	return(p);
}
#endif

/* result: 1 -> error; 0 -> success */
int translate2(int cpsolver_type,bool allow_unsupported,bool relaxed_labeling,vector<string> flist,string ofile) throw(runtime_error)
{	int n_files;
	char **files;
	struct node *program,*n;

	FILE *fpo;

	if (ofile=="-")
		fpo=stdout;
	else
	{	fpo=fopen(ofile.c_str(),"w");
		if (fpo==NULL)
		{	open_err(ofile);
		}
	}

	if (flist.size()==0)
	{	n_files=1;
		files=NULL;
	}
	else
	{	files=(char**)calloc(flist.size(),sizeof(char *));
		for(int i=0;i<(int)flist.size();i++)
			files[i]=strdup(flist[i].c_str());
		n_files=flist.size();
	}

//set_debug_parse(true);
	program=parse_program2(n_files,files);
//output_program(program);

#ifdef DEBUG_TREE
	debug_show_program(program);
#endif

	
	
	CSP *csp;

	csp=extract_csp(program);

	for(n=program->next;n!=NULL;n=n->next)
		fix_syntax(n->data,csp,cpsolver_type,allow_unsupported);

	output_csp(csp,fpo,cpsolver_type,relaxed_labeling);

/*
	extern char *trans_pl;
	fputs(trans_pl,fpo);

	extern char *exec_pl;
	fputs(exec_pl,fpo);

	extern char *dors_pl;
	fputs(dors_pl,fpo);
*/

	if (fpo!=stdout) fclose(fpo);

	return(0);
}

int translate2(int cpsolver_type,bool allow_unsupported,bool relaxed_labeling,string FILE,string ofile) throw(runtime_error)
{	vector<string> FILES;

	FILES.push_back(FILE);
	
	return(translate2(cpsolver_type,allow_unsupported,relaxed_labeling,FILES,ofile));
}


#ifdef COMPILE_TRANSLATE_MAIN
/* for dirname() */
#include <libgen.h>

void usage(void)
{	fprintf(stderr,"Usage: translate2 -3|-4|-bp|-swi|-gams|-minizinc|-gurobi [--allow-unsupported] [--relaxed-labeling] <file1> [<file2> [...]]\n");
	fprintf(stderr,"\n%s\n",library_notes);
}

int main(int argc,char *argv[])
{	vector<string> FILES;
	int cpsolver_type;
	bool relaxed_labeling;
	bool allow_unsupported;

	if (argc<=1)
	{	usage();
		exit(1);
	}

	if (strcmp(argv[1],"-3")==0)
		cpsolver_type=CPSOLVER_SICSTUS3;
	else
	if (strcmp(argv[1],"-4")==0)
		cpsolver_type=CPSOLVER_SICSTUS4;
	else
	if (strcmp(argv[1],"-bp")==0)
		cpsolver_type=CPSOLVER_BPROLOG;
	else
	if (strcmp(argv[1],"-swi")==0)
		cpsolver_type=CPSOLVER_SWIPROLOG;
	else
	if (strcmp(argv[1],"-gams")==0)
		cpsolver_type=CPSOLVER_GAMS;
	else
	if (strcmp(argv[1],"-minizinc")==0)
		cpsolver_type=CPSOLVER_MINIZINC;
	else
	if (strcmp(argv[1],"-gurobi")==0)
		cpsolver_type=CPSOLVER_GUROBI;
	else
	{	usage();
		exit(1);
	}

	/* skip the -3/-4 spec */
	argc--;
	argv++;

	allow_unsupported=false;
	if (strcmp(argv[1],"--allow-unsupported")==0)
	{	allow_unsupported=true;

		/* skip the --allow-unsupported spec */
		argc--;
		argv++;
	}

	relaxed_labeling=false;
	if (strcmp(argv[1],"--relaxed-labeling")==0)
	{	relaxed_labeling=true;

		/* skip the --relaxed-labeling spec */
		argc--;
		argv++;
	}

	for(int i=1;i<argc;i++)
		FILES.push_back(argv[i]);

	if (FILES.size()==0)
		FILES.push_back("-");

	int ret=translate2(cpsolver_type,allow_unsupported,relaxed_labeling,FILES);

	exit(ret);
}

#endif /* COMPILE_TRANSLATE_MAIN */
