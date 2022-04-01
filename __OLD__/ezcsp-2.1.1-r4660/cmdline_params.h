#ifndef EZCSP_CMDLINE_PARAMS_H
#define EZCSP_CMDLINE_PARAMS_H

#include <string>

#include "solver-types.h"

class cmdline_params
{
public:

	std::string EXE_DIR;	/* directory where ezcsp binary is located, as per arg0 of command line */

	bool QUIET;
	bool DEBUG;
	bool DEBUG_TIMES;
	bool SHOW_GROUNDER_STDERR;
	std::string AFLAG;
	int NMODELS;
	bool PREPARSE_ONLY;
	bool PRE_GROUNDED;
	bool MKATOMS;
	int cputime_limit;
	bool error_on_timeout;
	std::string SEARCH_STATE_IN,SEARCH_STATE_OUT;
	std::string CSP_CHOICES_IN,CSP_CHOICES_OUT;
	bool run_asp_only;
	bool show_encoding_only;
	bool show_cpsolver_output;
	bool save_search_state;
	bool load_search_state;
	bool merged_csp_choices;
	bool append_csp_choices;
	bool save_csp_choices;
	bool load_csp_choices;
	bool separate_translation;
	bool quick_translation;
	bool relaxed_labeling;
	bool allow_unsupported;
	bool skip_denials;
	int CPSOLVER_TYPE;
#ifdef HAVE_CMODELS
	bool use_cmodels_incremental;
	bool use_cmodels_feedback;
	std::string cmodels_lib_options;
#endif /* HAVE_CMODELS */
	bool pure;
	bool pure_monolithic;
	int bprolog_stack_size;
	bool bprolog_no_compile;
	std::string gams_solver;

	std::string GROUNDER;
	std::string GOPTS;
	std::string SOLVER;
	std::string CPSOLVER;
	std::string TRANSLATOR;

	cmdline_params();
	
	std::vector<std::string> processCmdLine(int argc,char **argv);
};

#endif /* EZCSP_CMDLINE_PARAMS_H */
