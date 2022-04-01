#include "config.h"

#include <iostream>

#include <string>
#include <vector>

/* for exit(), atoi() */
#include <stdlib.h>

/* for dirname() */
#include <libgen.h>

/* for strdup() */
#include <string.h>

#include "phpemu.h"
#include "common.h"

#include "library_notes.h"

#include "cmdline_params.h"

using namespace std;
using namespace phpemu;

cmdline_params::cmdline_params()
{	EXE_DIR=".";

	QUIET=false;
	DEBUG=false;
	DEBUG_TIMES=false;
	SHOW_GROUNDER_STDERR=false;
	AFLAG="";
	NMODELS=1;
	PREPARSE_ONLY=false;
	PRE_GROUNDED=false;
	MKATOMS=false;
	cputime_limit=0;
	error_on_timeout=true;
	run_asp_only=false;
	show_encoding_only=false;
	show_cpsolver_output=false;
	save_search_state=false;
	load_search_state=false;
	merged_csp_choices=false;
	append_csp_choices=false;
	save_csp_choices=false;
	load_csp_choices=false;
	separate_translation=true;
	quick_translation=true;
	relaxed_labeling=false;
	allow_unsupported=false;
	skip_denials=false;
	CPSOLVER_TYPE=CPSOLVER_BPROLOG;
#ifdef HAVE_CMODELS
	use_cmodels_incremental=false;
	use_cmodels_feedback=false;
	cmodels_lib_options="";
#endif /* HAVE_CMODELS */
	pure=false;
	pure_monolithic=false;
	bprolog_stack_size=0;
	bprolog_no_compile=false;
	gams_solver="LINDO";

	GROUNDER="gringo";
	GOPTS="";
	SOLVER="";
	CPSOLVER="";
	TRANSLATOR="translate2";
}

vector<string> cmdline_params::processCmdLine(int argc,char **argv)
{	int i;
	vector<string> FILES;

	if (argc==2 && ((string)argv[1])=="-h")
	{	cerr << "Usage: ezcsp [<options>] [[[--pure-file] <EZ file1>] [[--pure-file] <EZ file2>...]]" << endl;
		cerr << "          where <options> are:" << endl;
		cerr << "             --pre-grounded" << endl;
		cerr << "             --debug" << endl;
		cerr << "             --debug-exec" << endl;
		cerr << "             --debug-times" << endl;
		cerr << "             --show-grounder-stderr" << endl;
		cerr << "             --grounder <path>" << endl;
		cerr << "             --gopts <string>" << endl;
		cerr << "             --solver <path>" << endl;
#ifdef HAVE_CMODELS
		cerr << "             --cmodels-incremental[=<options>]" << endl;
		cerr << "             --cmodels-feedback[=<options>] (implies --cmodels-incremental)" << endl;
#endif /* HAVE_CMODELS */
		cerr << "             --translator <path>" << endl;
		cerr << "             --cpsolver <path>" << endl;
		cerr << "             --sicstus4|--sicstus3|--bprolog[:<stack size>]|--swiprolog|--gams[:<solver>]]|--minizinc|--gurobi" << endl;
		cerr << "                Default: --bprolog" << endl;
		cerr << "                Domains supported by the cp solvers:" << endl;
		cerr << "                    sicstus 4: fd, q, r" << endl;
		cerr << "                    sicstus 3: fd, q, r" << endl;
		cerr << "                    bprolog: fd, lp (linear programming)" << endl;
		cerr << "                    swiprolog: fd, q, r" << endl;
		cerr << "                    gams: all domains supported by GAMS" << endl;
		cerr << "                          gams solver defaults to LINDO" << endl;
		cerr << "                    minizinc: all domains supported by MiniZinc" << endl;
		cerr << "                          specify solver with --cpsolver (defaults to minizinc)" << endl;
		cerr << "                    gurobi: all domains supported by Gurobi" << endl;
		cerr << "                          specify solver with --cpsolver (defaults to python2)" << endl;
		cerr << "             --bprolog-no-compile" << endl;
		cerr << "             --relaxed-labeling" << endl;
		cerr << "             --allow-unsupported: allow constructs that are not supported by certain versions of selected CP solver" << endl;
		cerr << "             --skip-denials: do not use denials to force the ASP solver to find a new answer set if the CP solver fails." << endl;
		cerr << "                             WARNING: this will cause an infinite loop unless the ASP solver persists its state." << endl;
		cerr << "                             DO NOT USE unless you know what you are doing." << endl;
		cerr << "                             USE ezcsp-pstate.sh instead." << endl;
		cerr << "             -n <nmodels>" << endl;
		cerr << "             --mkatoms" << endl;
		cerr << "             -a" << endl;
		cerr << "             -q" << endl;
		cerr << "             --pure" << endl;
		cerr << "             --pure-monolithic" << endl;
		cerr << "             --run-asp-only" << endl;
		cerr << "             --show-encoding-only" << endl;
		cerr << "             --show-cpsolver-output" << endl;
		cerr << "             --cputime <secs>" << endl;
		cerr << "             --load-search-state <file>" << endl;
		cerr << "             --save-search-state <file>" << endl;
		cerr << "             --no-separate-translation-step" << endl;
		cerr << "             --no-quick-trans" << endl;
		cerr << "             --load-csp-choices <file>" << endl;
		cerr << "             --merged-csp-choices <file>" << endl;
		cerr << "             --save-csp-choices <file>" << endl;
		cerr << "             --append-csp-choices <file>" << endl;
		cerr << "       ezcsp --preparse-only" << endl;
		cerr << "       ezcsp -h" << endl;

		cerr << endl;
		cerr << library_notes;
		cerr << endl;

		exit(0);
	}

	char *arg0=strdup(argv[0]);	/* basename() and dirname() may alter the contents of the input parameter */
	if (strcmp(argv[0],basename(arg0))==0)	/* no path specified; using $PATH */
		EXE_DIR="";
	else
	{	strcpy(arg0,argv[0]);   /* basename() may have altered the contents of arg0 */
		EXE_DIR=string(dirname(arg0))+"/";
	}

	for(i=1;i<argc;i++)
	{	string arg;
	
		arg=argv[i];

		if (arg=="-n")
		{	i++;
			NMODELS=atoi(argv[i]);
		}
		else if (arg=="-a")
		{	AFLAG="-a";
		}
		else if (arg=="-q")
		{	QUIET=true;
		}
		else if (arg=="--debug")
		{	DEBUG=true;
		}
		else if (arg=="--debug-exec")
		{	set_cppsystem_debug(true);
		}
		else if (arg=="--debug-times")
		{	DEBUG_TIMES=true;
		}
		else if (arg=="--show-grounder-stderr")
		{	SHOW_GROUNDER_STDERR=true;
		}
		else if (arg=="--preparse-only")
		{	PREPARSE_ONLY=true;
		}
		else if (arg=="--pre-grounded")
		{	PRE_GROUNDED=true;
		}
		else if (arg=="--grounder")
		{	i++;
			GROUNDER=argv[i];
		}
		else if (arg=="--gopts")
		{	i++;
			GOPTS=argv[i];
		}
		else if (arg=="--solver")
		{	i++;
			SOLVER=argv[i];
		}
#ifdef HAVE_CMODELS
		else if (arg=="--cmodels-incremental" || startsWith(arg,"--cmodels-incremental="))
		{	size_t i;

			use_cmodels_incremental=true;
			i=arg.find("=");
			if (i!=string::npos)
				cmodels_lib_options=trim(arg.substr(i+1,string::npos),"\"");
		}
		else if (arg=="--cmodels-feedback" || startsWith(arg,"--cmodels-feedback="))
		{	size_t i;

			use_cmodels_incremental=true;
			use_cmodels_feedback=true;
			i=arg.find("=");
			if (i!=string::npos)
				cmodels_lib_options=trim(arg.substr(i+1,string::npos),"\"");
		}
#endif /* HAVE_CMODELS */
		else if (arg=="--cpsolver")
		{	i++;
			CPSOLVER=argv[i];
		}
		else if (arg=="--translator")
		{	i++;
			TRANSLATOR=argv[i];
		}
		else if (arg=="--sicstus3")
		{	CPSOLVER_TYPE=CPSOLVER_SICSTUS3;
		}
		else if (arg=="--sicstus4")
		{	CPSOLVER_TYPE=CPSOLVER_SICSTUS4;
		}
		else if (arg=="--swiprolog")
		{	CPSOLVER_TYPE=CPSOLVER_SWIPROLOG;
		}
		else if (arg=="--bprolog" || (startsWith(arg,"--bprolog:")))
		{	size_t p;

			CPSOLVER_TYPE=CPSOLVER_BPROLOG;
			if ((p=arg.find(':'))!=string::npos)
				bprolog_stack_size=atoi(arg.substr(p+1).c_str());
		}
		else if (arg=="--gams" || (startsWith(arg,"--gams:")))
		{	size_t p;

			CPSOLVER_TYPE=CPSOLVER_GAMS;
			if ((p=arg.find(':'))!=string::npos)
				gams_solver=arg.substr(p+1).c_str();
		}
		else if (arg=="--minizinc")
		{	CPSOLVER_TYPE=CPSOLVER_MINIZINC;
		}
		else if (arg=="--gurobi")
		{	CPSOLVER_TYPE=CPSOLVER_GUROBI;
		}
		else if (arg=="--bprolog-no-compile")
		{	bprolog_no_compile=true;
		}
		else if (arg=="--mkatoms")
		{	MKATOMS=true;
		}
		else if (arg=="--cputime")
		{	i++;
			cputime_limit=atoi(argv[i]);
		}
		else if (arg=="--noerror-on-timeout")
		{	error_on_timeout=false;
		}
		else if (arg=="--run-asp-only")
		{	run_asp_only=true;
		}
		else if (arg=="--show-encoding-only")
		{	show_encoding_only=true;
		}
		else if (arg=="--show-cpsolver-output")
		{	show_cpsolver_output=true;
		}
		else if (arg=="--load-search-state")
		{	i++;
			SEARCH_STATE_IN=argv[i];
			load_search_state=true;
		}
		else if (arg=="--save-search-state")
		{	i++;
			SEARCH_STATE_OUT=argv[i];
			save_search_state=true;
		}
		else if (arg=="--no-separate-translation-step")
		{	separate_translation=false;
		}
		else if (arg=="--no-quick-trans")
		{	quick_translation=false;
		}
		else if (arg=="--relaxed-labeling")
		{	relaxed_labeling=true;
		}
		else if (arg=="--allow-unsupported")
		{	allow_unsupported=true;
		}
		else if (arg=="--skip-denials")
		{	skip_denials=true;
		}
		else if (arg=="--load-csp-choices")
		{	i++;
			CSP_CHOICES_IN=argv[i];
			load_csp_choices=true;
		}
		else if (arg=="--merged-csp-choices")
		{	merged_csp_choices=true;
		}
		else if (arg=="--save-csp-choices")
		{	i++;
			CSP_CHOICES_OUT=argv[i];
			save_csp_choices=true;
		}
		else if (arg=="--append-csp-choices")
		{	i++;
			CSP_CHOICES_OUT=argv[i];
			append_csp_choices=true;
		}
		else if (arg=="--pure")
		{	pure=true;
		}
		else if (arg=="--pure-monolithic")
		{	pure=true;
			pure_monolithic=true;
		}
		else
			break;
	}

	if (SOLVER=="")
	{
#ifdef HAVE_CMODELS
		SOLVER=((use_cmodels_incremental) ? "cmodels":"clasp");
#else
		SOLVER="clasp";
#endif /* HAVE_CMODELS */
	}

	if (CPSOLVER=="")
	{	switch(CPSOLVER_TYPE)
		{	case CPSOLVER_SICSTUS3:
			case CPSOLVER_SICSTUS4:
				CPSOLVER="sicstus";
				break;
			case CPSOLVER_SWIPROLOG:
				CPSOLVER="swipl";
				break;
			case CPSOLVER_BPROLOG:
				CPSOLVER="bp";
				break;
			case CPSOLVER_GAMS:
				CPSOLVER="gams";
				break;
			case CPSOLVER_MINIZINC:
				CPSOLVER="minizinc";
			case CPSOLVER_GUROBI:
				CPSOLVER="python2";
				break;
		}
	}

	if (separate_translation && (load_csp_choices || save_csp_choices || append_csp_choices))
	{	cerr << "Error: --no-separate-translation-step MUST be specified" << endl;
		cerr << "       together with --load-csp-choices, --save-csp-choices and --append-csp-choices." << endl;
		cerr << "*** Aborting." << endl;
		exit(1);
	}
	if (save_csp_choices && append_csp_choices)
	{	cerr << "Error: --save-csp-choices and --append-csp-choices cannot " << endl;
		cerr << "be specified together." << endl;
		cerr << "*** Aborting." << endl;
		exit(1);
	}
	if (merged_csp_choices && !load_csp_choices)
	{	cerr << "Error: --merged-csp-choices requires --load-csp-choices." << endl;
		cerr << "*** Aborting." << endl;
		exit(1);
	}
	for(;i<argc;i++)
	{	if (string(argv[i])=="--pure-file")
		{	i++;
			if (i<argc)
				FILES.push_back(string("^&^")+argv[i]);
		}
		else
			FILES.push_back(argv[i]);
	}
	return(FILES);
}
