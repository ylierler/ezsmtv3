#ifndef EZCSP_CP_SOLVER_H
#define EZCSP_CP_SOLVER_H

#include <string>
#include <vector>

#include "cmdline_params.h"

extern float cp_solver_time;

bool call_cp_solver(cmdline_params p,std::string PL_TRANS,std::string TFILE1,std::string TFILE2,std::string CSP_MOD,std::vector<std::string> DEBUG_FILES);

/* Returns total time spent in CP solver */
float total_cp_solver_time(void);

/* ++x = v
 * matches[1]=x
 * matches[2]=v
 */
bool is_cp_equality_statement(std::string line,std::vector<std::string> &matches);
/* ++x </>/<=/>=... v
 * matches[1]=x
 * matches[2]=symbol
 * matches[3]=v
 */
//bool is_cp_inequality_statement(string line,vector<string> &matches);
/* ++ (followed by anything)
 * matches[1]=whatever follows "++"
 */
bool is_cp_statement(std::string line,std::vector<std::string> &matches);

void reset_solutions_found(std::string DEST_FILE);
void mark_solution_found(std::string SOLUTION,std::string DEST_FILE);


#endif /* EZCSP_CP_SOLVER_H */
