// Copyright (C) 2009-2021 Marcello Balduccini. All Rights Reserved.
//
// Runs the ezcsp solver (ASP+CSP with unmodified solvers).
// The ezcsp solver iteratively computes one answer set and
// checks if the csp constraints required by the answer set
// are satisfied. If they are not, the algorithm iterates.
//
// Usage (OBSOLETE -- check function below):
//        ezcsp [<options>] [[--pure-file] <EZ file1> [[--pure-file] <EZ file2>...]]
//           where <options> are:
//             --pre-grounded
//             --debug-exec
//             --debug-times
//             --show-grounder-stderr
//             --grounder <path>
//             --gopts <string>
//             --solver <path>
//             --cmodels
//             --cpsolver <path>
//             [--sicstus3|--bprolog[:<stack size>]]
//             -n <nmodels>
//             --mkatoms
//             -a
//             -q
//             --pure
//	       --pure-monolithic
//             --run-asp-only
//             --show-encoding-only
//             --show-cpsolver-output
//             --cputime <secs>
//             --noerror-on-timeout
//             --load-search-state <file>
//             --save-search-state <file>
//             --no-separate-translation-step
//             --no-quick-trans
//             --load-csp-choices <file>
//             --merged-csp-choices <file>
//             --save-csp-choices <file>
//             --append-csp-choices <file>
//        ezcsp --preparse-only
//        ezcsp -h
//

/*
 *-------------------------------------
 *   
 *
 *   History
 *  ~~~~~~~~~
 *   04/27/21 - [2.1.1] Support added for gurobi (experimental).
 *   07/28/18 - [2.0.1] Fixed bug in generation of constraint programs.
 *   05/03/17 - [2.0.0] New predicate names adopted (required, var).
 *                      Support added for Prolog queries and rules inside
 *                      required(). Domain "query" added as synonym of fd.
 *   04/19/17 - [1.8.5] Support for sqr(float) in minizinc added.
 *   04/17/17 - [1.8.4] Support for ASP solvers with persistent state added
 *                      via option --skip-denials.
 *   04/11/17 - [1.8.3] Support for sum constraint in minizinc improved.
 *   04/10/17 - [1.8.2] Support for cumulative in minizinc added.
 *   04/09/17 - [1.8.1] Support for minizinc logical operators added.
 *   04/08/17 - [1.8.0] Support for minizinc cp solver format added.
 *   04/04/17 - [1.7.12] Workaround added for sum/3 not supported in 
 *                       B-Prolog 8.1 clp(fd).
 *   03/10/17 - [1.7.11] \/ now supported in BProlog thanks to workaround
 *                       provided by Neng-Fa Zhou.
 *   03/09/17 - [1.7.10] Detection of constructs unsupported by certain
 *                       versions of CP solver selected, e.g. \/ in
 *                       B-Prolog 7.5+. Option --allow_unsupported added 
 *                       to allow the use of such constructs.
 *   11/15/16 - [1.7.9] Option --relax-labeling added for clp(q) and
 *                      clp(r).
 *   11/10/16 - [1.7.8] Fixes to the pre-parsing algorithm to support
 *                      all versions of gringo.
 *   11/02/16 - [1.7.7] Added abs, pow, exp, sin, cos, tan to GAMS.
 *   09/30/16 - [1.7.6] Fixed error in encoding for SWI-Prolog that
 *                      caused incorrect handling of -n flag.
 *   01/04/16 - [1.7.5] Fixed handling of escaped double quotes in
 *                      mkatoms-style output.
 *   12/17/15 - [1.7.4] Fixed error in outputting constraints
 *                      for bounds stated by cspvar/3.
 *   12/16/15 - [1.7.3] Some string handling errors fixed.
 *   12/12/15 - [1.7.2] Error fixed in generation of GAMS input.
 *   12/12/15 - [1.7.1] Support for sum functor added to GAMS.
 *   12/10/15 - [1.7.0] Support for GAMS solver added via option
 *                      --gams[:<solver>].
 *   12/05/15 - [1.6.24b] Typos in configuration script fixed. Thanks
 *                        Benjamin Susman <bsusman@unomaha.edu>.
 *   10/21/15 - [1.6.24] Added ** and div for numerical constraints.
 *   10/12/15 - [1.6.23] Cmodels support improvements.
 *   10/03/15 - [1.6.22] Support for SWI-Prolog (--swiprolog) added.
 *                       Support for sum constraint added in Q, R, LP.
 *                       Q and R encodings now attempt to find values
 *                       for all variables (sound but incomplete).
 *                       #verbatim now moved to dlv_rsig.
 *                       "#begin_verbatim." and "#end_verbatim." added.
 *   09/30/15 - [1.6.21] Detection of failure in B-Prolog's LP solver
 *                       fixed.
 *   01/12/15 - [1.6.20b61] EZCSP can now be compiled under MacOS.
 *   01/12/15 - [1.6.20b60] Cmodels must be set up explicitly with
 *                          --with-cmodels in ./configure.
 *   07/03/13 - [1.6.20b59] Made compatible with gringo-4.
 *   04/23/13 - [1.6.20b58] Performance improvements.
 *   04/19/13 - [1.6.20b57] Ignore Prolog's exit status when the
 *                          program produced a valid output.
 *                          Prolog's exit status is unreliable on
 *                          some systems.
 *   04/19/13 - [1.6.20b56] Do not pass "prolog_" facts to Prolog
 *                          if they are under strong negation, since
 *                          they are generally not supported.
 *   04/18/13 - [1.6.20b55] When using --bprolog, the Prolog code is
 *                          now compiled before execution. This prevents
 *                          the generation of temp file __tmp.out by
 *                          by B-Prolog, which is dangerous in shared
 *                          volumes. Compilation also appears to make
 *                          execution faster overall.
 *                          To disable the compilation, use
 *                          --bprolog-no-compile.
 *                          Also added a hostid from gethostid()
 *                          to the temp filenames in an attempt to
 *                          reduce conflicts on shared volumes.
 *   04/06/13 - [1.6.20b54] Options can now be passed to cmodels in
 *                          incremental and feedback modes with
 *                          --cmodels-incrementa=<opts> and
 *                          --cmodels-feedback=<opts>.
 *   04/02/13 - [1.6.20b53] Ezcsp now outputs the size of the grounding
 *                          (before any denials added at run-time).
 *   04/01/13 - [1.6.20b52] Ezcsp now outputs the time spent in the
 *                          CP solver.
 *   03/27/13 - [1.6.20b51] Introduced directive "#verbatim " to tell
 *                          the pre-parser to not attempt any parsing of
 *                          the rest of the line -- useful in the defined
 *                          part to avoid ezcsp to return syntax errors.
 *                          Example:
 *                            #verbatim :- table reachable_from/3, connected_to/4.
 *                          The part "table reachable_from/3" is not
 *                          legal ezcsp syntax.
 *   03/13/13 - [1.6.20b50] Some models were not generated in blackbox
 *                          mode in some cases.
 *   03/08/13 - [1.6.20b49] Grounding time and total time are now displayed.
 *   02/13/13 - [1.6.20b48] Defined part can now be passed regular
 *                          atoms as "input" by using relations prefixed
 *                          by "prolog_". The occurrence of at least one
 *                          cspvar atom in the program is no longer 
 *                          a requirement.
 *                          Corrected error in generation of denials
 *                          with --cmodels-feedback.
 *   01/18/13 - [1.6.20b47] Corrected error in detection of
 *                          inconsistent programs as determined
 *                          by cmodels.
 *   01/17/13 - [1.6.20b46] Corrected handling of relations in the
 *                          scope of lists when using --cmodels-feedback.
 *                          cmodels >=3.83 REQUIRED.
 *   11/19/12 - [1.6.20b45] Corrected handling of implication
 *                          when BProlog is used.
 *   11/08/12 - [1.6.20b44] Various bugfixes. Handling of errors
 *                          in CP solver execution improved.
 *                          --cmodels-incremental.
 *   05/08/12 - [1.6.20b43] Options --cmodels-feedback and --debug
 *                          added. --cmodels-feedback implies
 *                          --cmodels-incremental.
 *   04/30/12 - [1.6.20b42] Iterative feedback now caches positive
 *                          literals in the latestquery from cmodels
 *                          to avoid useless calls to CSP solver.
 *   03/05/12 - [1.6.20b41] Adding support for "iterative feedback"
 *                          with cmodels. Not yet functional.
 *                          Cpu time reported under Windows/mingw32
 *                          now correct (on lightly-loaded cpus).
 *   02/29/12 - [1.6.20b40] Fixed error in call to cmodels.
 *                          Some code for "interactive feedback"
 *                          is in place.
 *   08/25/11 - [1.6.20b39] When using cmodels, denials are now
 *                          added only if cmodels hasn't already
 *                          reported that there are no further
 *                          models. Otherwise, the current
 *                          version of cmodels crashes.
 *   06/27/11 - [1.6.20b38] Added support for floating point
 *                          numbers. Floating point numbers are
 *                          processed so that they are treated
 *                          as constants by the ASP solver but
 *                          are used as numbers by the CP solver.
 *                          When using -a option, cspeq relations
 *                          are formatted so that if the second
 *                          argument is a floating point number,
 *                          it is surrounded by double quotes for
 *                          compatibility with ASP solvers. In any
 *                          other case, quote addition does not
 *                          take place.
 *   06/21/11 - [1.6.20b37] Support for Q and R domains restored.
 *   06/20/11 - [1.6.20b36] ezcsp can now be compiled for windows
 *                          with mingw32.
 *   06/14/11 - [1.6.20b35] Added final statistics with number of
 *                          backtrackings from CP to ASP.
 *   06/06/11 - [1.6.20b34] Now ezcsp looks for auxiliary binaries
 *                          in the same directory where ezcsp is located
 *                          (as per argv[0] on the command line).
 *   05/19/11 - [1.6.20b33] Added support for specifying a defined part,
 *                          i.e. Prolog code defining relations which
 *                          can occur inside required/1, e.g.
 *                          required(p(a))
 *                          where a is a CSP variable and p is defined in:
 *                          #begin_defined.
 *                          p(X) :- X #> 10.
 *                          p(X) :- X #< 2.
 *                          #end_defined.
 *   05/19/11 - [1.6.20b32] Added support for LP/MIP's lp_integer and
 *                          lp_solve with min/max of objective function.
 *                          Added support for cspvar with arity 1,
 *                          which declares a variable without specifying
 *                          a domain for it.
 *   05/18/11 - [1.6.20b31] Added support for LP/MIP under B-Prolog.
 *                          lp_integer not supported yet.
 *   02/23/11 - [1.6.20b30] Allowed extensional lists in
 *			 relation required, e.g.
 *			   required(cumulative([st(T1),st(T2)],[D1,D2],[1,1],1)) :-
 *				  disj(T1,T2),
 *				  task(T1,D1),
 *				  task(T2,D2).
 *                       Now using dlv_rsig 1.8.1 to correct the
 *                       precedence of reified csp operators.
 *                       Added clp(fd) implication as [#]-> and [#]<-.
 *                       Modified to allow using older versions of Sicstus
 *                       (e.g. 3.8.x).
 *                       Added support for cumulative/4 in Sicstus 4.x.
 *                       Added support for disjoint2/4.
 *                       Added ability to specify path to sicstus.
 *                       Added support for minimum/2 and maximum/2.
 *                       Option --separate-translation-step restored.
 *                       Added option --no-quick-trans.
 *                       Translation to sicstus completely rewritten,
 *                       now implemented directly in C++.
 *                       Option --separate-translation-step replaced
 *                       by --no-separate-translation-step.
 *                       Option --sicstus3 added.
 *                       Added support for B-Prolog; option --bprolog added.
 *                       Integration with cmodels completed. Use option
 *                       --cmodels to use cmodels instead of a regular solver.
 *                       Implemented various efficiency improvements.
 *                       CP solver now called only if cspvar relation
 *                       is defined in the corresponding answer set.
 *                       ezcsp now works correctly in the presence of
 *                       #hide statements (csp-relevant relations are
 *                       forced to be always shown).
 *                       Added option -q.
 *                       Added patch to circumvent bug in BProlog when the
 *                       cumulative global constraint is called with information
 *                       for only one job.
 *                       Added option --pure.
 *                       Added support for specifying Prolog lists in
 *                       global constraints by means of relations, whose last 
 *                       argument is the element to be added. If the element 
 *                       is the name of a csp variable, then the variable is
 *                       used. Otherwise, the element is interpreted as a constant.
 *                       Added support for disjoint2 when --bprolog is used.
 *                       Added option --pure-monolithic.
 *                       Added per-file option --pure-file, which says that
 *                       the file does not contain any ezcsp syntactic sugar
 *                       and does not need to be pre-parsed.
 *   01/27/11 - [1.6.19] Now cspdomain(fd) is assumed by default.
 *   09/17/10 - [1.6.18] Changes to improve performance on file handling.
 *   09/09/10 - [1.6.17] Added support for sin, cos, tan, pow, exp.
 *   04/15/10 - [1.6.16] Generation of multiple models for domains r and q
 *                       corrected.
 *   04/15/10 - [1.6.15] Support of domains q and r revised and improved.
 *   04/10/10 - [1.6.14] Major improvements to the saving and loading
 *                       of choices. By "choices" now we mean both the
 *                       selection choices and the enumeration choices.
 *   03/11/10 - [1.6.13] Added option --append-csp-choices to write the
 *			 solver's choices without overwriting an existing
 *			 file. Loading and saving of solver's choices
 *			 modified to take into account information on
 *			 enumeration decisions (i.e. choices about values),
 *			 and not just selection decisions (i.e. choices
 *			 of variables). As a result, loading and saving
 *			 of choices is NOW SUPPORTED ONLY FOR "ff"
 *			 SELECTION HEURISTIC.
 *   02/25/10 - [1.6.12] Added options --load-csp-choices and 
 *			 --save-csp-choices. The choices made by the constraint
 *			 solver that lead directly to the solution are,
 *			 respectively, saved to file and loaded. The choices
 *			 that were later backtracked upon are not saved.
 *			 When the choices are loaded, the constraint solver is
 *			 forced to make those same choices (although later it
 *			 can backtrack), and the options specified with
 *			 label_option/1 are ignored (options used are
 *			 [ff,bisect,up,all]). The options are not supported
 *			 when --separate-translation-step is used.
 *   02/17/10 - [1.6.11] Support added for the specification of options for
 *			 Sicstus' labeling/2 predicate via the addition
 *			 of relation label_option/1,
 *			 e.g.label_option(ff). label_option(down).
 *   11/04/09 - [1.6.10] Support for negation of reified constraints added
 *                       (#! in EZCSP, #\ in Sicstus Prolog).
 *   11/03/09 - [1.6.9] Prolog translation modified for compatibility with
 *                      Sicstus 4.x. WARNING: cumulative/4 is not available
 *                      in Sicstus 4.x!!
 *   10/21/09 - [1.6.8] Added option --noerror-on-timeout to have ezcsp
 *                      terminate without error upon timeout, but just
 *                      with whatever models have been found (or with no model).
 *   10/19/09 - [1.6.7] Combined translation to Prolog and execution of the
 *                      CLP program in a single call to SICStus. On a
 *                      medium-sized experiment, execution of ezcsp went
 *                      from ~2sec to ~1sec. Added command line option
 *                      --separate-translation-step to run the two steps
 *                      separately (mainly for debugging purposes).
 *   10/19/09 - [1.6.6] Major changes to the translation to Sicstus to reduce
 *                      even further the chances of hitting Sicstus' limit of
 *                      256 permanent variables in a clause.
 *   10/16/09 - [1.6.5] Changed translation to reduce the chances of hitting
 *                      Sicstus' limit of 256 permanent variables in a clause.
 *   10/16/09 - [1.6.4] Added --show-encoding-only command-line option.
 *                      Added CSP definition relation label_order(Var,Num),
 *                      which allows to specify in which order the
 *                      CSP variables will be in the labeling/2 statement
 *                      of the Prolog encoding of the CSP.
 *                      Added --cputime option. Now sicstus is run with
 *                      a timeout only if --cputime is specified.
 *   10/07/09 - [1.6.3] Added passing of --mkatoms -a options to crmodels2
 *                      (requires crmodels2 version 2.0.3 or later).
 *   10/06/09 - [1.6.2] Added termination cleanup hook.
 *   10/06/09 - [1.6.1] Added mapping of global constraint names (sum).
 *                      Now renaming is done by adding prefix "ezcsp__"
 *                      instead of "x_".
 *   10/01/09 - [1.6.0] Added the ability to save the search state upon
 *                      termination, and to load it back upon start.
 *                      Default programs changed to gringo and clasp.
 *   07/31/09 - [1.5] Added aliases for reified csp constraint operators
 *                    (e.g. \/ for #\/, /\ for #/\).
 *   07/31/09 - [1.4] Added support for CR-Prolog programs.
 *   07/29/09 - [1.3] Added support for reified csp constraint operators
 *                    (#\/, #/\, etc.).
 *
 */
 
#include "config.h"

#include <iostream>
#include <iomanip> /* for setiosflags() and setprecision() */
#include <fstream>

#include <string>
#include <vector>

/* for dirname() */
#include <libgen.h>

/* for exit(), atoi() */
#include <stdlib.h>

#if HAVE_SYS_WAIT_H
# include <sys/wait.h>
#else
#  ifndef WIFSIGNALED
#    undef _W_INT
#    ifdef _POSIX_SOURCE
#      define	_W_INT(i)	(i)
#    else
#      define	_W_INT(w)	(*(int *)(void *)&(w))	/* convert union wait to int */
#      undef WCOREFLAG
#      define	WCOREFLAG	0200
#    endif
#    undef _WSTATUS
#    define	_WSTATUS(x)	(_W_INT(x) & 0177)
#    undef _WSTOPPED
#    define	_WSTOPPED	0177		/* _WSTATUS if process is stopped */
#    define WIFSIGNALED(x)	(_WSTATUS(x) != _WSTOPPED && _WSTATUS(x) != 0)
#    define WTERMSIG(x)	(_WSTATUS(x))
#  endif
#endif
#if HAVE_SYS_RESOURCE_H
#  include <sys/resource.h>
#endif
#if HAVE_SIGNAL_H
#  include <signal.h>
#endif

#if HAVE_SIGNAL_H
#  include <sys/stat.h>
#endif

#include "phpemu.h"

#include "common.h"

#include "translate.h"

#include "pre-parser.h"

#include "solver-types.h"

#include "cmdline_params.h"

#include "asp_solver.h"
#include "cp_solver.h"

#include "search_state.h"

#include "output_model.h"

#ifdef HAVE_CMODELS
/* for testPartialSolutionInfo */
#include "ctable.h"
#endif /* HAVE_CMODELS */

#include "versions.h"	/* SVN release and status */
#define EZCSP_VERSION "2.1.1"
//"_"__TIMESTAMP__"_"

using namespace std;
using namespace phpemu;

vector<string> ALL_FILES;

void file_cleanup(void)
{	rm_all_files(ALL_FILES);
}

void sig_termination_handler(int signum)
{	fprintf(stderr,"*** Aborted\n");
	exit(1);
}

void setup_termination_traps(void)
{
#ifndef _WIN32
	struct sigaction new_action, old_action;
#endif

	/* Set up atexit() trap so that we can remove
	 * the temp files when the program exits with exit().
	 */
	atexit(file_cleanup);


	/* Now let's take care of termination signals. */     

#ifndef _WIN32
	/* Set up the structure to specify the new action. */
	new_action.sa_handler = sig_termination_handler;
	sigemptyset (&new_action.sa_mask);
	new_action.sa_flags = 0;
     
	sigaction (SIGINT, NULL, &old_action);
	if (old_action.sa_handler != SIG_IGN)
		sigaction (SIGINT, &new_action, NULL);
	sigaction (SIGHUP, NULL, &old_action);
	if (old_action.sa_handler != SIG_IGN)
		sigaction (SIGHUP, &new_action, NULL);
	sigaction (SIGTERM, NULL, &old_action);
	if (old_action.sa_handler != SIG_IGN)
		sigaction (SIGTERM, &new_action, NULL);
#endif
}

int call_crprolog(cmdline_params p,char *argv0,string TFILE1)
{	int ret;

//	cppsystem("cp "+TFILE1+" qqq");

	string mkatoms_opts="";
	string extra_solver_opts="";

	if (p.MKATOMS)
		mkatoms_opts="--mkatoms "+p.AFLAG;

	switch(p.CPSOLVER_TYPE)
	{	case CPSOLVER_SICSTUS3:
			extra_solver_opts+="--sicstus3 ";
			break;
		case CPSOLVER_SWIPROLOG:
			extra_solver_opts+="--swiprolog ";
			break;
		case CPSOLVER_BPROLOG:
			extra_solver_opts+="--bprolog";
			if (p.bprolog_stack_size>0)
				extra_solver_opts+=":"+toString(p.bprolog_stack_size);
			extra_solver_opts+=" ";
		/* SICSTUS4 is default */
	}
	extra_solver_opts+="--cpsolver \'"+p.CPSOLVER+"\' ";
	if (p.QUIET)
		extra_solver_opts+="-q ";
	if (!p.separate_translation)
		extra_solver_opts+="--no-separate-translation-step ";
	if (!p.quick_translation)
		extra_solver_opts+="--no-quick-trans ";
	if (p.show_encoding_only)
		extra_solver_opts+="--show-encoding-only ";
	if (p.load_csp_choices)
		extra_solver_opts+="--load-csp-choices \'"+p.CSP_CHOICES_IN+"\' ";
	if (p.save_csp_choices)
		extra_solver_opts+="--save-csp-choices \'"+p.CSP_CHOICES_OUT+"\' ";
	if (p.append_csp_choices)
		extra_solver_opts+="--append-csp-choices \'"+p.CSP_CHOICES_OUT+"\' ";

	set_cputime_limit(0);	// left crmodels2 handle timeouts
	ret=cppsystem("crmodels2 "+mkatoms_opts+
		" --cputime-aware-solver --cputime "+toString(p.cputime_limit)+
		" --grounder \""+p.GROUNDER+
		"\" --solver \""+((string)argv0)+
		" --pre-grounded -a "+extra_solver_opts+
		"\" --state-aware-solver "+toString(p.NMODELS)+" "+TFILE1);

	return(ret);
}

class shortcut_exception : public std::runtime_error
{
public:
	explicit shortcut_exception(const std::string & __arg)
				   : runtime_error(__arg) { }
};

#ifdef HAVE_CMODELS
class ezcsp_tsp : public testPartialSolutionInfo
{
public:
	cmdline_params p;
	string ASP_MOD,TFILE1,DEF_PART,CP_SOLS,PL_TRANS,TFILE2,CSP_MOD;
	string INPUT;

	ezcsp_tsp() : latest_assignment(NULL), latest_assignment_size(0)
	{}
	~ezcsp_tsp()
	{	if (latest_assignment)
		{	free(latest_assignment);
			latest_assignment=NULL;
			latest_assignment_size=0;
		}
	}

	bool testPartialSolution(int *external_assignment,int num_ext_assigned);

private:
	int *latest_assignment;
	int latest_assignment_size;
	bool latest_result;
} tpsInfo;

bool ezcsp_tsp::testPartialSolution(int *external_assignment,int num_ext_assigned)
{	int count;
	int *assignment;
	int i;

	if (p.DEBUG) cerr << "WARNING: ezcsp_tsp::testPartialSolution() ASSUMES that external_assignment is ordered by increasing ABSOLUTE VALUE of its elements." << std::endl;

	assignment=(int *)calloc(num_ext_assigned,sizeof(int));
	/* drop all the (NAF-)negated literals */
	for(i=0,count=0;i<num_ext_assigned;i++)
	{	if (external_assignment[i]>=0)
			assignment[count++]=external_assignment[i];
	}

	if (latest_assignment)
	{	if (count == latest_assignment_size && memcmp(assignment,latest_assignment,count*sizeof(int))==0)
		{	free(assignment);

			if (p.DEBUG) cerr << "ezcsp_tsp::testPartialSolution() detected duplicate query. Reporting cached result of " << (latest_result ? "FEASIBLE":"UNfeasible") << std::endl;

			return(latest_result);
		}
	}

	free(latest_assignment);
	latest_assignment=assignment;
	latest_assignment_size=count;

	reset_solutions_found(CP_SOLS); /* this must occur *BEFORE* translate_to_csp() because translate_to_csp() may add data to it */


	if (p.DEBUG) cerr << endl << "got from cmodels " << num_ext_assigned << " assignments" << endl;
	count=output_like_mkatoms(p,INPUT,latest_assignment,latest_assignment_size,TFILE1);
//	count=output_like_mkatoms(INPUT,external_assignment,num_ext_assigned,TFILE1);
//	count=output_like_mkatoms(INPUT,external_assignment,num_ext_assigned,ASP_MOD);

	if (count==0)	// is it trivially feasible?
	{	if (p.DEBUG) cerr << "trivially feasible. reporting FEASIBLE" << endl;
		return(true);
	}

	if (p.DEBUG)
	{	cerr << "WARNING:" << endl;
		cerr << "  copy of external_assignments is in ./ext-assgn.txt" << endl;
		cppsystem("cp "+TFILE1+" ./ext-assgn.txt");
		cerr << "assignments: " << endl;
		cppsystem("cat "+TFILE1 +" >&2");
		cerr << "----------" << endl;
	}

	/* Translate the CSP definition from the answer set into a CSP */
	if (!translate_to_csp(p,ASP_MOD,TFILE1,DEF_PART,CP_SOLS,PL_TRANS))
	{	rm_all_files(ALL_FILES);
		exit(1);
	}

	if (p.DEBUG)
	{	cerr << "CP program is:" << endl;
		cppsystem("cat "+PL_TRANS +" >&2");
		cerr << "----------" << endl;
	}

	/* call CP solver */
	vector<string> DEBUG_FILES;
	DEBUG_FILES.push_back(DEF_PART);
	DEBUG_FILES.push_back(CP_SOLS);
	if (call_cp_solver(p,PL_TRANS,TFILE1,TFILE2,CSP_MOD,DEBUG_FILES))
	{
		if (p.DEBUG) cerr << "reporting FEASIBLE!" << endl;
		latest_result=true;
		return(true);
	}

	if (p.DEBUG) cerr << "reporting UNfeasible" << endl;

	latest_result=false;
	return(false);

}

void passFiles(cmdline_params p,string ASP_MOD,string TFILE1,string DEF_PART,string CP_SOLS,string PL_TRANS,string TFILE2,string CSP_MOD)
{	tpsInfo.p=p;
	tpsInfo.ASP_MOD=ASP_MOD;
	tpsInfo.TFILE1=TFILE1;
	tpsInfo.DEF_PART=DEF_PART;
	tpsInfo.CP_SOLS=CP_SOLS;
	tpsInfo.PL_TRANS=PL_TRANS;
	tpsInfo.TFILE2=TFILE2;
	tpsInfo.CSP_MOD=CSP_MOD;
}
#endif /* HAVE_CMODELS */

int main(int argc,char **argv)
{
	fstream fp,fpo;

	string TDIR;
#ifdef __MINGW32__
	char *tmpdir=getenv("TEMP");
	TDIR=tmpdir;
	if (tmpdir==NULL)
#endif
	TDIR="/tmp";
	//
	string PARSED=new_tmpfname(TDIR+"/tezcsp-0-");
	string ASP_MOD=new_tmpfname(TDIR+"/tezcsp-1-");
	string TFILE1=new_tmpfname(TDIR+"/tezcsp-2-");
	string CSP_MOD=new_tmpfname(TDIR+"/tezcsp-3-");
	string PREV_ASP_MODELS=new_tmpfname(TDIR+"/tezcsp-4-");
	string PL_TRANS=new_tmpfname(TDIR+"/tezcsp-5-");
	string TFILE2=new_tmpfname(TDIR+"/tezcsp-6-");
	string CP_SOLS=new_tmpfname(TDIR+"/tezcsp-7-");
	string DEF_PART=new_tmpfname(TDIR+"/tezcsp-8-");

	//vector<string> ALL_FILES;
	//
	ALL_FILES.push_back(PARSED);
	ALL_FILES.push_back(ASP_MOD);
	ALL_FILES.push_back(TFILE1);
	ALL_FILES.push_back(CSP_MOD);
	ALL_FILES.push_back(PREV_ASP_MODELS);
	ALL_FILES.push_back(PL_TRANS);
	ALL_FILES.push_back(TFILE2);
	ALL_FILES.push_back(CP_SOLS);
	ALL_FILES.push_back(DEF_PART);
	/* The use of compile-and-load (cl/1) in B-Prolog
	 * will cause the creation of extra temp files
	 * <PL_TRANS>.out, <CP_SOLS>.out, <DEF_PART>.out.
	 * We add their names to ALL_FILES, so they
	 * can eventually be removed.
	 */
	ALL_FILES.push_back(PL_TRANS+".out");
	ALL_FILES.push_back(CP_SOLS+".out");
	ALL_FILES.push_back(DEF_PART+".out");

	bool alg_result;
	bool csp_state_valid;

	cmdline_params p;

	int i,ret;
	int MODELS;

	int cp_to_asp_backtracks;
	float grounding_time;
	bool grounding_time_available=false;
	long grounding_size;
	bool grounding_size_available=false;

	setup_termination_traps();

	vector<string> FILES=p.processCmdLine(argc,argv);
	vector<bool> PURE_FILES;
	for(int i=0;i<(int)FILES.size();i++)
	{	if (startsWith(FILES[i],"^&^"))
		{	PURE_FILES.push_back(false);
			FILES[i]=FILES[i].substr(3);
		}
		else
			PURE_FILES.push_back(true);
	}

	if (!p.QUIET)
		clog << "ezcsp version " << EZCSP_VERSION 
		     << SVN_REL
		     << "..." 
		     << endl;

	if (p.cputime_limit>0)
	{	set_cputime_limit(p.cputime_limit);

		set_error_on_timeout(p.error_on_timeout);
	}

#ifdef HAVE_CMODELS
	if (p.use_cmodels_feedback)
	{	/* pass the filenames to the ASP solver in case it is interactive */
		passFiles(p,ASP_MOD,TFILE1,DEF_PART,CP_SOLS,PL_TRANS,TFILE2,CSP_MOD);

		/* warn uses about certain restrictions of
		 * --cmodels-feedback
		 */
		clog << "WARNING: when using --cmodels-feedback, the relations occurring in the scope " << endl
		     << "         of CSP []-style lists must be domain predicates." << endl;
	}
#endif /* HAVE_CMODELS */

	cp_to_asp_backtracks=0;
	MODELS=0;
	csp_state_valid=false;
	alg_result=true;
	try
	{
		if (!p.PRE_GROUNDED)
		{	bool is_crprolog;

			if (p.pure && p.NMODELS==1
#ifdef HAVE_CMODELS
				 && !p.use_cmodels_incremental
#endif /* HAVE_CMODELS */
			    )
			{	string f;

				f="";
				for(int i=0;i<(int)FILES.size();i++)
					f=f+"\""+FILES[i]+"\" ";

				if (p.pure_monolithic)
					ret=timed_cppsystem(p.SOLVER+" "+p.GOPTS+" "+f+" > \""+ASP_MOD+"\"");
				else
					ret=timed_cppsystem(p.GROUNDER+" "+p.GOPTS+" "+f+" | "+p.SOLVER +" > \""+ASP_MOD+"\"");

				alg_result=output_pure_aset(p,ASP_MOD,TFILE1,MODELS);
				if (alg_result)
					MODELS++;

				throw shortcut_exception("");
			}
			else
			if (p.pure)
			{	string redir;

				if (FILES.size()==0)
					FILES.push_back("-");
				redir=">";
				for(int i=0;i<(int)FILES.size();i++)
				{	cppsystem("cat "+FILES[i]+" "+redir+" "+TFILE1);
					redir=">>";
				}
			}
			else
			{	ezcsp_preparse(FILES,PURE_FILES,TFILE1,"-",DEF_PART,&is_crprolog); // send stderr to console
				if (p.PREPARSE_ONLY)
				{	readfile(TFILE1);
					rm_all_files(ALL_FILES);
					exit(0);
				}
			
				if (is_crprolog)
				{	ret=call_crprolog(p,argv[0],TFILE1);
					rm_all_files(ALL_FILES);
					exit(ret);
				}
			}

			// ground the program
			ret=timed_cppsystem(p.GROUNDER+" "+p.GOPTS+" < \""+TFILE1+"\"  > \""+PARSED+"\" 2> \""+TFILE2+"\"",grounding_time);
			grounding_time_available=true;
			if (ret != 0) // error
			{	cerr << "*** Error during execution of the grounder:" << endl;
				myreadfile(PARSED,&cerr);
				myreadfile(TFILE2,&cerr);
				cerr << "***<---- End of output" << endl;
				rm_all_files(ALL_FILES);
				exit(1);
			}
			struct stat st;
			stat(PARSED.c_str(),&st);
			grounding_size = st.st_size;
			grounding_size_available=true;
			if (p.SHOW_GROUNDER_STDERR)
				readfile(TFILE2);
		}
		else
		{	/* All input files have already been grounded.
			 * Just copy them to PARSED.
			 */
			
			fp.open(PARSED.c_str(),ios::out | ios::trunc);
			if (fp.fail())
			{	open_err(PARSED);
			}
			if (FILES.size()==0)
				myreadfile("",&fp);
			else
			{	for(i=0;i<(int)FILES.size();i++)
					myreadfile(FILES[i],&fp);
			}
			fp.close();
		}

		/* create empty PREV_ASP_MODELS file */
		fp.open(PREV_ASP_MODELS.c_str(),ios::out | ios::trunc);
		if (fp.fail())
		{	open_err(PREV_ASP_MODELS);
			//rm_all_files(ALL_FILES);
			//exit(1);
		}
		fp.close();

		if (p.load_search_state)
			load_search_state_asp(p.SEARCH_STATE_IN,PREV_ASP_MODELS);

		while(p.NMODELS == 0 || MODELS < p.NMODELS)
		{	bool pure_asp;
			bool some_solution_found;

			csp_state_valid=false;

			merge_files(PREV_ASP_MODELS,PARSED,TFILE1);

#ifdef HAVE_CMODELS
			if (p.use_cmodels_feedback)
			{	asp_solver_set_tpsInfo(&tpsInfo);
				tpsInfo.INPUT=TFILE1;	/* the file that is used as input to the ASP solver */
			}
#endif /* HAVE_CMODELS */

			pure_asp=true;
			/* call ASP solver */
			if (!call_asp_solver(p,TFILE1,ASP_MOD,&pure_asp,p.pure,MODELS))
			{	alg_result=false;
				break;
			}

			if (pure_asp)
			{	output_pure_aset(p,ASP_MOD,TFILE1,MODELS);

				some_solution_found=true;
				MODELS=MODELS + 1;
			}
			else
			{
				reset_solutions_found(CP_SOLS); /* this must occur *BEFORE* translate_to_csp() because translate_to_csp() may add data to it */

				/* Translate the CSP definition from the answer set into a CSP */
				if (!p.run_asp_only && !translate_to_csp(p,ASP_MOD,TFILE1,DEF_PART,CP_SOLS,PL_TRANS))
				{	rm_all_files(ALL_FILES);
					exit(1);
				}
				some_solution_found=false;
				csp_state_valid=true;
				while(p.NMODELS==0 || MODELS<p.NMODELS)
				{	

					if (p.DEBUG_TIMES)
						clog << "Before constraint solver: " << date() << endl;

					if (p.run_asp_only)
					{	output_aset(p,ASP_MOD,TFILE1,MODELS);
						output_extended_aset_footer(p);

						MODELS=MODELS + 1;

						csp_state_valid=false;
						break;
					}

					if (p.show_encoding_only)
					{	string cmt="%";
						switch(p.CPSOLVER_TYPE)
						{	case CPSOLVER_GAMS:
								cmt="*";
								break;
							case CPSOLVER_GUROBI:
								// For Gurobi we write a Python program.
								// However, using regular "#" comments
								// interacts badly with the comment
								// "Encoding: x" that ezcsp generates.
								// To work around it, we use this
								// as comment string:
								cmt="''''''#";
								break;
							default:
								cmt="%";
								break;
						}
						cout << cmt << " Encoding: " << (MODELS+1) << endl;
						cout << cmt << " Program: " << endl;
						myreadfile(PL_TRANS,&cout);
						cout << cmt << " End of program" << endl;
						cout << cmt << " Auxiliary file: " << DEF_PART << " (defined part)" << endl;
						myreadfile(DEF_PART,&cout);
						cout << cmt << " End of auxiliary file: " << DEF_PART << endl;
						cout << cmt << " Auxiliary file: " << CP_SOLS << " (previous CP solutions)" << endl;
						myreadfile(CP_SOLS,&cout);
						cout << cmt << " End of auxiliary file: " << CP_SOLS << endl;
						MODELS=MODELS + 1;

						csp_state_valid=false;
						break;
					}

					/* call CP solver */
					vector<string> DEBUG_FILES;
					DEBUG_FILES.push_back(DEF_PART);
					DEBUG_FILES.push_back(CP_SOLS);
					if (!call_cp_solver(p,PL_TRANS,TFILE1,TFILE2,CSP_MOD,DEBUG_FILES))
					{	cp_to_asp_backtracks++;
						csp_state_valid=false;
						break;
					}

					output_extended_aset(p,ASP_MOD,CSP_MOD,TFILE1,MODELS);

					mark_solution_found(CSP_MOD,CP_SOLS);

					some_solution_found=true;
					MODELS=MODELS + 1;
				}
			}

			if (p.NMODELS != 0 && MODELS >= p.NMODELS)
			{	// Exit as quickly as possible if we are done finding models.
				break;
			}

			// Create a denial to reject the ASP model just computed
			if (!p.skip_denials)
				append_denial(p,ASP_MOD,PARSED,TFILE1,PREV_ASP_MODELS,some_solution_found);
		}
	}
	catch(shortcut_exception& e)
	{	/* do nothing */
	}
	catch(timeout_error& e)
	{	cerr << e.what() << endl;
		rm_all_files(ALL_FILES);
		exit(2);
	}
	catch(runtime_error& e)
	{	cerr << e.what() << endl;
		rm_all_files(ALL_FILES);
		exit(1);
	}
	
	if (MODELS == 0 && p.MKATOMS)
	{	if (p.AFLAG!="")
			cout << "%*** no models found." << endl;
		else
			cout << "*** no models found." << endl;
	}

	if (!p.MKATOMS && !p.show_encoding_only)
	{	cout << ((alg_result) ? "True":"False") << endl;
		cout << "Duration: " << setiosflags(ios::fixed) << setprecision(3) << get_total_cpu() << endl;
		if (grounding_time_available)
			cout << "  Grounding time: " << setiosflags(ios::fixed) << setprecision(3) << grounding_time << endl;
		cout << "  CP Solver time: " << setiosflags(ios::fixed) << setprecision(3) << total_cp_solver_time() << endl;
		if (grounding_size_available)
			cout << "Grounding size: " << grounding_size << endl;
		cout << "Number of CP-to-ASP backtrackings: " << cp_to_asp_backtracks << endl;
	}

	if (p.save_search_state)
		store_search_state(p.SEARCH_STATE_OUT,PREV_ASP_MODELS,CP_SOLS,csp_state_valid);

	rm_all_files(ALL_FILES);

	exit(0);
}
