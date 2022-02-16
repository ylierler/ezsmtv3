#ifndef EZCSP_TRANSLATE_2_MINIZINC_H
#define EZCSP_TRANSLATE_2_MINIZINC_H

// Copyright (C) 2009-2021 Marcello Balduccini. All Rights Reserved.

#include <string>
#include <vector>

#include <exception>
#include <stdexcept>

#include "defs.h"

#include "translate2.h"

extern struct syntax_map map_mzn[];

void output_csp_constraint_MZN(CSP *csp,int i,struct item *req,FILE *fpo,int cpsolver_type);

void output_csp_MZN(CSP *csp,FILE *fpo,int cpsolver_type);


#endif /* EZCSP_TRANSLATE_2_MINIZINC_H */
