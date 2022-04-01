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
struct syntax_map map_mzn[]=
	{	{ (char *)">", (char *)"ezcsp__gt", FOR_ANY_SOLVER, true },

		{ (char *)">=", (char *)"ezcsp__geq", FOR_ANY_SOLVER, true },

		{ (char *)"<", (char *)"ezcsp__lt", FOR_ANY_SOLVER, true },

		{ (char *)"<=", (char *)"ezcsp__leq", FOR_ANY_SOLVER, true },

		{ (char *)"=", (char *)"ezcsp__eq", FOR_ANY_SOLVER, true },

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



void output_csp_constraint_MZN(CSP *csp,int i,struct item *req,FILE *fpo,int cpsolver_type)
{	fprintf(fpo,"constraint ");

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

void output_csp_MZN(CSP *csp,FILE *fpo,int cpsolver_type)
{
	/* Enable support for cumulative. 
	 * Do we need something similar for the other global constraints as well?
	 * NOTE: cumulative gives error with mzn-gecode, but works with minizinc and mzn-g12fd.
	 */
	fprintf(fpo,"include \"cumulative.mzn\";\n");

	// vars
	const char *vartype=(csp->domain=="fd") ? "int":"float";

	for(int i=0;i<(int)csp->cspvar.size();i++)
	{	struct item *v;

		v=csp->cspvar[i];
		int idx=get_var_index(csp,v->args[0]);
		if (idx==0)
		{	clog << "ERROR: unknown variable with term " << v->args[0]->relation << endl;
			exit(1);
		}
		fprintf(fpo,"var %s: X%d;\n",vartype,idx);
	}
	fprintf(fpo,"\n");

	// constr
	for(int i=0;i<(int)csp->required.size();i++)
	{	fprintf(fpo,"%% ");
		output_atom_to_file(csp->required[i],fpo);
		fprintf(fpo,"\n");
		output_csp_constraint_MZN(csp,i+1,csp->required[i],fpo,cpsolver_type);
	}
	for(int i=0;i<(int)csp->cspvar.size();i++)
	{	struct item *v;

		v=csp->cspvar[i];
		if (v->arity==3)
		{	int idx=get_var_index(csp,v->args[0]);
			fprintf(fpo,"constraint X%d >= %s ;\n",idx,v->args[1]->relation);
			fprintf(fpo,"constraint X%d <= %s ;\n",idx,v->args[2]->relation);
		}
	}
	fprintf(fpo,"\n");

	if (csp->domain=="nlp")
	{	fprintf(fpo,"function var float: sqr(var float:x) = pow(x,2);\n");
	}
	fprintf(fpo,"\n");

	fprintf(fpo,"solve satisfy;\n");

	for(int i=0;i<(int)csp->labeling.size();i++)
	{	fprintf(fpo,"output [\"++");
		output_atom_to_file(csp->labeling[i],fpo);
		fprintf(fpo,"=\\(X%d)\\n\"];\n",i+1);
	}
	fprintf(fpo,"output [\"++succeeded\\n\"];\n");

	// output value assignments to the .lst file
/*	fprintf(fpo,"file output/ '' / ;\n");
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
*/
}
