#ifndef EZCSP_ASP_SOLVER_H
#define EZCSP_ASP_SOLVER_H

#include <string>

#include "cmdline_params.h"

#ifdef HAVE_CMODELS
/* for testPartialSolutionInfo */
#include "ctable.h"
#endif /* HAVE_CMODELS */

bool call_asp_solver(cmdline_params p,std::string INPUT,std::string ASP_MOD,bool *pure_asp,bool forced_pure_asp,int MODELS);
void append_denial(cmdline_params p,std::string ASP_MOD,std::string PARSED,std::string TFILE1,std::string DEST,bool full_model);
#ifdef HAVE_CMODELS
void asp_solver_set_tpsInfo(testPartialSolutionInfo *tpsi);
#endif /* HAVE_CMODELS */
/* outputs only the positive literals, e.g. not under "not".
 * returns the number of literals output.
 */
int output_like_mkatoms(cmdline_params p,std::string PARSED,int *cmodels_assignments,int num_assignments,std::string OUTPUT_FILE);

#endif /* EZCSP_ASP_SOLVER_H */
