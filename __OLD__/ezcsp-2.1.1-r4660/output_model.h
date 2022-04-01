#ifndef EZCSP_OUTPUT_MODEL_H
#define EZCSP_OUTPUT_MODEL_H

#include <string>

#include "cmdline_params.h"

void output_aset(cmdline_params p,std::string ASP_MOD,std::string TFILE1,int MODELS);
void output_csp_solution(cmdline_params p,std::string CSP_MOD);
void output_extended_aset_footer(cmdline_params p);
/*
 * Returns false if no model; true otherwise.
 */
bool output_pure_aset(cmdline_params p,std::string ASP_MOD,std::string TFILE1,int MODELS);
void output_extended_aset(cmdline_params p,std::string ASP_MOD,std::string CSP_MOD,std::string TFILE1,int MODELS);


#endif /* EZCSP_OUTPUT_MODEL_H */
