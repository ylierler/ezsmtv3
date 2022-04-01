// by Marcello Balduccini [040817]
// Copyright (C) 2009-2021 Marcello Balduccini. All Rights Reserved.
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

#include "phpemu.h"

#include "common.h"

#include "solver-types.h"

#include "cp_solver.h"

#include "cp_solver_gurobi.h"

using namespace std;
using namespace phpemu;


/*
 * Returns true if a solution was found 
 (and stored in CSP_MOD) and false otherwise.
 */
bool call_cp_solver_GUROBI(cmdline_params p,string PL_TRANS,string TFILE1,string TFILE2,string CSP_MOD,vector<string> DEBUG_FILES)
{	string load_flag="";
	int ret;
	float call_time=0.0;

	extern vector<string> ALL_FILES;


	if (cpprename(PL_TRANS,PL_TRANS+".lp")!=0)
	{	cerr << "***Error while renaming " << PL_TRANS << " to " << PL_TRANS << ".mzn" << endl;
		rm_all_files(ALL_FILES);
		exit(1);
	}

	ret=cppsystem(p.CPSOLVER+" "+PL_TRANS+".lp > \""+TFILE1+"\" 2>\""+TFILE2+"\"",call_time); // 2> /dev/null
	cp_solver_time+=call_time;

	if (cpprename(PL_TRANS+".lp",PL_TRANS)!=0)
	{	cerr << "***Error while renaming " << PL_TRANS << ".lp to " << PL_TRANS << endl;
		rm_all_files(ALL_FILES);
		exit(1);
	}

	if (p.DEBUG_TIMES)
		clog << "After constraint solver: " << date() << endl;

	// merge stdout and stderr -- stdout comes LAST
	// we also convert the output from Gurobi's format
	merge_files(TFILE2,TFILE1,CSP_MOD);

	if (p.show_cpsolver_output)
	{	cout << "Output of the CP solver:" << endl;
		myreadfile(CSP_MOD,&cout);
		cout << "------------End of output" << endl;
	}

	bool grep_failed=false;
	bool grep_succeeded=false;

	if (my_grep_startsWith("Error:",CSP_MOD,1,false,false))
		ret=1;
	else
	{	grep_failed=my_grep_startsWith("++failed",CSP_MOD,1,false,false);
		if (!grep_failed)
			grep_succeeded=my_grep_startsWith("++succeeded",CSP_MOD,1,false,false);
	}

	if (ret!=0)
	{	// then there was some execution error
		cerr << "***Error while executing the GAMS program:" << endl;
		myreadfile(PL_TRANS,&cerr);
		cerr << "***<---- Program end." << endl;
		for(int i=0;i<DEBUG_FILES.size();i++)
		{	cerr << "***Extra file " << DEBUG_FILES[i] << ":" << endl;
			myreadfile(DEBUG_FILES[i],&cerr);
			cerr << "***<---- end of " << DEBUG_FILES[i] << endl;
		}
		cerr << "***Result was:" << endl;
		myreadfile(TFILE2,&cout);
		myreadfile(CSP_MOD,&cerr);
		cerr << "***<---- Result end." << endl;
		rm_all_files(ALL_FILES);
		exit(1);
	}

	if (grep_failed) return(false);
	if (grep_succeeded) return(true);

	return(true);
}
