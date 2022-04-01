#ifndef EZCSP_CP_SOLVER_MINIZINC_H
#define EZCSP_CP_SOLVER_MINIZINC_H

#include <string>
#include <vector>

#include "cmdline_params.h"

#include "cp_solver.h"

bool call_cp_solver_MZN(cmdline_params p,std::string PL_TRANS,std::string TFILE1,std::string TFILE2,std::string CSP_MOD,std::vector<std::string> DEBUG_FILES);

#endif /* EZCSP_CP_SOLVER_MINIZINC_H */
