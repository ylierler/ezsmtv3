#ifndef EZCSP_PREPARSER_H
#define EZCSP_PREPARSER_H

// by Marcello Balduccini [051009]
//
// Copyright (C) 2009-2021 Marcello Balduccini. All Rights Reserved.

#include <string>
#include <vector>

void ezcsp_preparse(std::vector<std::string> flist,std::vector<bool> fpure_list,std::string ofile,std::string efile,std::string defpart_file,bool *is_crprolog);
void ezcsp_preparse(std::vector<std::string> flist,std::vector<bool> fpure_list,std::string ofile,std::string efile,std::string defpart_file);

#endif /* EZCSP_PREPARSER_H */
