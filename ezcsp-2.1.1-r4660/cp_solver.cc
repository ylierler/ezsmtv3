#include "config.h"

#include <fstream>
#include <iostream>

#include <string>
#include <vector>

/* for exit(), atoi() */
#include <stdlib.h>

#include "common.h"

#include "phpemu.h"

#include "cp_solver.h"

#include "cp_solver_minizinc.h"

#include "cp_solver_gurobi.h"

using namespace std;
using namespace phpemu;

float cp_solver_time=0.0;

float total_cp_solver_time(void)
{	return(cp_solver_time);
}

/*
 * Returns true if a solution was found 
 (and stored in CSP_MOD) and false otherwise.
 */
bool call_cp_solver_GAMS(cmdline_params p,string PL_TRANS,string TFILE1,string TFILE2,string CSP_MOD,vector<string> DEBUG_FILES)
{	string load_flag="";
	int ret;
	float call_time=0.0;


	ret=cppsystem(p.CPSOLVER+" "+PL_TRANS+" SOLVER="+p.gams_solver+" Pagecontr=2 Pagesize=0 LOGOPTION=3 OUTPUT=\""+TFILE2+"\" > \""+CSP_MOD+"\"",call_time); // 2> /dev/null
	cp_solver_time+=call_time;

	if (p.DEBUG_TIMES)
		clog << "After constraint solver: " << date() << endl;

	if (p.show_cpsolver_output)
	{	cout << "Output of the CP solver:" << endl;
		myreadfile(TFILE2,&cout);
		myreadfile(CSP_MOD,&cout);
		cout << "------------End of output" << endl;
	}

	bool grep_failed=false;
	bool grep_succeeded=false;
	
	grep_failed=my_grep_startsWith("++failed",CSP_MOD,1,false,false);
	if (!grep_failed)
		grep_succeeded=my_grep_startsWith("++succeeded",CSP_MOD,1,false,false);

	if (ret!=0)
	{	extern vector<string> ALL_FILES;
		// then there was some execution error
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

/*
 * Returns true if a solution was found 
 (and stored in CSP_MOD) and false otherwise.
 */
bool call_cp_solver(cmdline_params p,string PL_TRANS,string TFILE1,string TFILE2,string CSP_MOD,vector<string> DEBUG_FILES)
{	string load_flag="";
	int ret;
	float call_time=0.0;

	if (p.CPSOLVER_TYPE==CPSOLVER_GAMS)
		return(call_cp_solver_GAMS(p,PL_TRANS,TFILE1,TFILE2,CSP_MOD,DEBUG_FILES));

	if (p.CPSOLVER_TYPE==CPSOLVER_MINIZINC)
		return(call_cp_solver_MZN(p,PL_TRANS,TFILE1,TFILE2,CSP_MOD,DEBUG_FILES));

	if (p.CPSOLVER_TYPE==CPSOLVER_GUROBI)
		return(call_cp_solver_GUROBI(p,PL_TRANS,TFILE1,TFILE2,CSP_MOD,DEBUG_FILES));

	switch(p.CPSOLVER_TYPE)
	{	case CPSOLVER_SICSTUS3:
		case CPSOLVER_SICSTUS4:
			load_flag="-l \""+fix_slashes(PL_TRANS)+"\"";
			break;
		case CPSOLVER_SWIPROLOG:
			load_flag="-g \"['"+fix_slashes(PL_TRANS)+"']\"";
			break;
		case CPSOLVER_BPROLOG:
			if (p.bprolog_no_compile)
				load_flag="-g \"['"+fix_slashes(PL_TRANS)+"']\"";
			else
			{	// use compile-and-load (cl/1) to
				// prevent B-Prolog from generating
				// a temp file "__tmp.out" in the
				// current directory when it
				// encounters a table directive.
				// Such a file may cause conflicts
				// when multiple instances of
				// ezcsp are being run.
				load_flag="-g \"cl('"+fix_slashes(PL_TRANS)+"')\"";
			}
			if (p.bprolog_stack_size>0)
				load_flag+=" -s "+toString(p.bprolog_stack_size);
			break;
	}
	ret=cppsystem(p.CPSOLVER+" "+load_flag+" > \""+TFILE1+"\" 2>\""+TFILE2+"\"",call_time); // 2> /dev/null
	cp_solver_time+=call_time;

	if (p.DEBUG_TIMES)
		clog << "After constraint solver: " << date() << endl;

	// merge stdout and stderr -- stdout comes LAST
	merge_files(TFILE2,TFILE1,CSP_MOD);

	if (p.show_cpsolver_output)
	{	cout << "Output of the CP solver:" << endl;
		myreadfile(CSP_MOD,&cout);
		cout << "------------End of output" << endl;
	}

	bool grep_failed=false;
	bool grep_succeeded=false;
	
	grep_failed=my_grep_startsWith("++failed",CSP_MOD,1,false,false);
	if ((!grep_failed) && (p.CPSOLVER_TYPE==CPSOLVER_BPROLOG))
	{	/* B-Prolog's LP solver does not fail explicitly, but outputs:
		 *          PROBLEM HAS NO FEASIBLE SOLUTION
		 * So, we need to check for that string in the output.
		 */
		grep_failed=my_grep_startsWith("PROBLEM HAS NO FEASIBLE SOLUTION",CSP_MOD,1,false,false);
	}

	if (!grep_failed)
		grep_succeeded=my_grep_startsWith("++succeeded",CSP_MOD,1,false,false);

	/* if we got ++failed or ++succeeded, we ignore the exit status of B-Prolog,
	 * because in some systems it is unreliable.
	 */
	if (grep_failed) return(false);
	if (grep_succeeded) return(true);

	extern vector<string> ALL_FILES;
	// then there was some execution error
	cerr << "***Error while executing the Prolog program:" << endl;
	myreadfile(PL_TRANS,&cerr);
	cerr << "***<---- Program end." << endl;
	for(int i=0;i<DEBUG_FILES.size();i++)
	{	cerr << "***Extra file " << DEBUG_FILES[i] << ":" << endl;
		myreadfile(DEBUG_FILES[i],&cerr);
		cerr << "***<---- end of " << DEBUG_FILES[i] << endl;
	}
	cerr << "***Result was:" << endl;
	myreadfile(CSP_MOD,&cerr);
	cerr << "***<---- Result end." << endl;
	rm_all_files(ALL_FILES);
	exit(1);

	return(true);
}

bool is_cp_equality_statement(string line,vector<string> &matches)
{	return(preg_match("\\+\\+(.*[a-zA-Z0-9')])=(-\?[0-9.a-z(][0-9.a-z,()]*)$",line,matches));
}

/*
bool is_cp_inequality_statement(string line,vector<string> &matches)
{	return(preg_match("\\+\\+(.*[a-zA-Z0-9')])([^0-9.a-z]*)([0-9.a-z(][0-9.a-z,()]*)$",line,matches));
}
*/

bool is_cp_statement(string line,vector<string> &matches)
{	return(!startsWith(line,"++succeeded") && preg_match("\\+\\+(.*)$",line,matches));
}

void reset_solutions_found(string DEST_FILE)
{	fstream fp,fpo;

	fpo.open(DEST_FILE.c_str(),ios::out | ios::trunc);
	if (fpo.fail())
	{	open_err(DEST_FILE);
		//rm_all_files(ALL_FILES);
		//exit(1);
	}
	fpo.close();
}

void mark_solution_found(string SOLUTION,string DEST_FILE)
{	fstream fp,fpo;

	fpo.open(DEST_FILE.c_str(),ios::out | ios::app);
	if (fpo.fail())
	{	open_err(DEST_FILE);
		//rm_all_files(ALL_FILES);
		//exit(1);
	}

	fpo << "skip_solution([" << endl;
	string SEP="";
	fp.open(SOLUTION.c_str(),ios::in);
	if (fp.fail())
	{	open_err(SOLUTION);
		//rm_all_files(ALL_FILES);
		//exit(1);
	}

	while(!fp.eof())
	{	vector<string> matches;
		string line;

		getline(fp,line);
		if (fp.fail()) break;

		line=trim(line);

		//if (preg_match("^\\+\\+(.*)=([0-9.]*).*",line,matches))
//		if (preg_match("\\+\\+(.*[a-zA-Z0-9')])=([0-9.a-z(][0-9.a-z,()]*).*",line,matches))
		if (is_cp_equality_statement(line,matches))
		{	fpo << SEP << " ( " << matches[1] << ", " << matches[2] << " )" << endl;
			SEP=",";
		}
/*		else
		if (is_cp_inequality_statement(line,matches))
		{	fpo << SEP << " ( " << matches[1] << matches[2] << matches[3] << " )" << endl;
			SEP=",";
		}
*/		else
		if (is_cp_statement(line,matches))
		{	fpo << SEP << " ( " << matches[1] << " )" << endl;
			SEP=",";
		}
	}
	fp.close();
	fpo << "])." << endl;

	fpo.close();
}
