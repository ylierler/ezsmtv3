// by Marcello Balduccini [040817]
// Copyright (C) 2009-2021 Marcello Balduccini. All Rights Reserved.
//
// Translates a set of literals containing a CSP definition
// into a MiniZinc encoding.
// Each literal must be ground and followed by a "." (e.g. "mkatoms -a" format).
// Double-quotes can be used for quoting.
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

#include "cp_solver.h"

#include "translate2.h"

using namespace std;
using namespace phpemu;

#define FOR_ANY_SOLVER 0
// Recall that gurobi's LP format does not distinguish between strict and non-strict inequalities
struct syntax_map map_gurobi[]=
	{	{ (char *)">", (char *)"ezcsp__gt", FOR_ANY_SOLVER, true },

		{ (char *)">=", (char *)"ezcsp__geq", FOR_ANY_SOLVER, true },

		{ (char *)"<", (char *)"ezcsp__lt", FOR_ANY_SOLVER, true },

		{ (char *)"<=", (char *)"ezcsp__leq", FOR_ANY_SOLVER, true },

		{ (char *)"==", (char *)"ezcsp__eq", FOR_ANY_SOLVER, true },

		{ (char *)"!=", (char *)"ezcsp__neq", FOR_ANY_SOLVER, true },

		{ (char *)"+", (char *)"ezcsp__pl", FOR_ANY_SOLVER, true },
		{ (char *)"-", (char *)"ezcsp__mn", FOR_ANY_SOLVER, true },
		{ (char *)"*", (char *)"ezcsp__tm", FOR_ANY_SOLVER, true },
		{ (char *)"/", (char *)"ezcsp__dv", FOR_ANY_SOLVER, true },
//		{ (char *)"**", (char *)"ezcsp__starstar", FOR_ANY_SOLVER, false },
		{ (char *)"div", (char *)"ezcsp__div", FOR_ANY_SOLVER, false },
		{ (char *)"mod", (char *)"ezcsp__mod", FOR_ANY_SOLVER, false },
		{ (char *)"max", (char *)"ezcsp__max", FOR_ANY_SOLVER, false },
		{ (char *)"min", (char *)"ezcsp__min", FOR_ANY_SOLVER, false },
		{ (char *)"abs", (char *)"ezcsp__abs", FOR_ANY_SOLVER, false },
		{ (char *)"pow", (char *)"ezcsp__pow", FOR_ANY_SOLVER, false },
		{ (char *)"exp", (char *)"ezcsp__exp", FOR_ANY_SOLVER, false },
		{ (char *)"sin", (char *)"ezcsp__sin", FOR_ANY_SOLVER, false },
		{ (char *)"cos", (char *)"ezcsp__cos", FOR_ANY_SOLVER, false },
		{ (char *)"tan", (char *)"ezcsp__tan", FOR_ANY_SOLVER, false },


		{ (char *)"\\/", (char *)"ezcsp__or", FOR_ANY_SOLVER, true },
		{ (char *)"/\\", (char *)"ezcsp__and", FOR_ANY_SOLVER, true },
		{ (char *)"xor", (char *)"ezcsp__xor", FOR_ANY_SOLVER, true },
		{ (char *)"<->", (char *)"ezcsp__diff", FOR_ANY_SOLVER, true },
		{ (char *)"not", (char *)"ezcsp__not", FOR_ANY_SOLVER, true },
		{ (char *)"->", (char *)"ezcsp__impl_r", FOR_ANY_SOLVER, true },
		{ (char *)"<-", (char *)"ezcsp__impl_l", FOR_ANY_SOLVER, true },

		//{ (char *)"sum", (char *)"ezcsp__sum", FOR_ANY_SOLVER, false },

		/*
		 * Functors that must be expanded later.
		 * Syntax: !!<op>:<neutral element>
		 */
		{ (char *)"!!+:0", (char *)"ezcsp__sum", FOR_ANY_SOLVER, false },

		{ NULL, NULL}
	};


void output_csp_constraint_GUROBI(CSP *csp,int i,struct item *req,FILE *fpo,int cpsolver_type)
{	vector<int> vars;
	vars=replace_ezcsp_vars(csp,req);

	expand_functor(req);

	// nth
//	for(int i=0;i<(int)vars.size();i++)
//		fprintf(fpo,"\t%s(%d, Q, X%d),\n",nth_rel[cpsolver_type],vars[i],vars[i]);

	fprintf(fpo,"    m.addConstr(");
	output_atom_to_file(req->args[0],fpo);
	fprintf(fpo,")\n");

	//fprintf(fpo,"\n");
}


// File format description:
//    https://www.gurobi.com/documentation/9.1/refman/model_file_formats.html
void output_csp_GUROBI(CSP *csp,FILE *fpo,int cpsolver_type)
{

	// vars
	const char *vartype=(csp->domain=="fd") ? "GRB.INTEGER":"GRB_CONTINUOUS";

	fprintf(fpo,"\
import gurobipy as gp\n\
from gurobipy import GRB\n\
\n\
try:\n\
    m = gp.Model('ezcsp')\n\
");
	for(int i=0;i<(int)csp->cspvar.size();i++)
	{	struct item *v;

		v=csp->cspvar[i];
		int idx=get_var_index(csp,v->args[0]);
		if (idx==0)
		{	clog << "ERROR: unknown variable with term " << v->args[0]->relation << endl;
			exit(1);
		}
		if (v->arity==3)
			fprintf(fpo,"    X%d = m.addVar(vtype=%s,lb=%s,ub=%s,name='X%d')\n",idx,vartype,v->args[1]->relation,v->args[2]->relation,idx);
		else if (v->arity==1)
			fprintf(fpo,"    X%d = m.addVar(vtype=%s,name='X%d')\n",idx,vartype,idx);
	}
	fprintf(fpo,"\n");

	// constr
	for(int i=0;i<(int)csp->required.size();i++)
	{	fprintf(fpo,"    # ");
		output_atom_to_file(csp->required[i],fpo);
		fprintf(fpo,"\n");
		output_csp_constraint_GUROBI(csp,i+1,csp->required[i],fpo,cpsolver_type);
	}

//	fprintf(fpo,"solve satisfy;\n");
	fprintf(fpo,"\
    m.optimize()\n\
\n\
    if m.Status == GRB.OPTIMAL:\n\
        print('++succeeded')\n\
    else:\n\
        print('++failed')\n\
\n\
");
	for(int i=0;i<(int)csp->labeling.size();i++)
	{	fprintf(fpo,"    print('++");
		output_atom_to_file(csp->labeling[i],fpo);
		fprintf(fpo,"=%%g' %% ( X%d.x ))\n",i+1);
	}

	fprintf(fpo,"\
\n\
    print('# Objective value: %%g' %% m.objVal)\n\
\n\
except gp.GurobiError as e:\n\
    print('Error code ' + str(e.errno) + ': ' + str(e))\n\
\n\
except AttributeError as e:\n\
    print('Encountered an attribute error: ' + str(e))\n\
");
}
