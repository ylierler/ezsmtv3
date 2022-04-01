#ifndef EZCSP_TRANSLATE_H
#define EZCSP_TRANSLATE_H

// by Marcello Balduccini [050709]
//
// Copyright (C) 2009-2021 Marcello Balduccini. All Rights Reserved.

#include <string>
#include <vector>

#include <exception>
#include <stdexcept>

#include "defs.h"

//#include "solver-types.h"

#include "cmdline_params.h"

//using namespace std;

/* FILES is an array of filenames; each "-" filename is stdin */
//int translate(std::string translator,std::string CPSOLVER,int cpsolver_type,std::vector<std::string> FILES,bool quick_trans,bool relaxed_labeling,bool *append_footer,std::string ofile="") throw(std::runtime_error);

/* FILE is a filename or "-" for stdin */
//int translate(std::string translator,std::string CPSOLVER,int cpsolver_type,std::string FILE,bool quick_trans,bool relaxed_labeling,bool *append_footer,std::string ofile="") throw(std::runtime_error);

/*
 * Returns false if the translation failed. True otherwise.
 */
bool translate_to_csp(cmdline_params p,std::string ASP_MOD,std::string TFILE1,std::string DEFPART,std::string CP_SOLS,std::string PL_TRANS);

#endif /* EZCSP_TRANSLATE_H */
