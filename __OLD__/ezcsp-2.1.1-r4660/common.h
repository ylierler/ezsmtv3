#ifndef EZCSP_COMMON_H
#define EZCSP_COMMON_H

// by Marcello Balduccini [050709]
//
// Copyright (C) 2009-2021 Marcello Balduccini. All Rights Reserved.

#include <string>
#include <vector>

#include <exception>
#include <stdexcept>

#include "defs.h"

//using namespace std;

void rm_all_files(std::vector<std::string> all_files);

void open_err(std::string file) throw(std::runtime_error);

void merge_files(std::string file1,std::string file2,std::string ofile) throw(std::runtime_error);

// if convert_ASP_to_Prolog == true, then
// we turn " into ' because smodels uses " for strings and sicstus uses '
// MUST BE CHANGED DEPENDING ON ASP and CSP solver
//
// if file=="", input is from stdin
void myreadfile(std::string file,std::ostream *fpo,bool convert_ASP_to_Prolog=false) throw(std::runtime_error);

// if convert_ASP_to_Prolog == true, then
// we turn " into ' because smodels uses " for strings and sicstus uses '
// MUST BE CHANGED DEPENDING ON ASP and CSP solver
//
// if file=="", input is from stdin
void myreadfile_ASP_to_Prolog(std::string file,std::ostream *fpo) throw(std::runtime_error);

std::string toString(std::vector<std::string> arr);

std::string toString(int i);

bool startsWith(const std::string s,const std::string prefix);
bool startsWith(const char *s,const char *prefix);

bool my_egrep(std::string exp,std::string file,bool invert_match=false,bool display=true) throw(std::runtime_error);

/* Like my_egrep, but no regular expressions, and
 * looking for a string at the beginning of the line.
 *
 * max_occurrences is the maximum number of occurrences
 * we want to find.
 * max_occurrences=0 means find all occurrences.
 *
 */
bool my_grep_startsWith(std::string prefix,std::string file,int max_occurrences=1,bool invert_match=false,bool display=true) throw(std::runtime_error);

/* Like my_egrep, but no regular expressions, and
 * looking for a string at the beginning of the *first* line.
 */
bool my_grep_startsWith_firstLine(std::string prefix,std::string file,bool invert_match=false,bool display=true) throw(std::runtime_error);

std::string date(void);

bool is_floating_point(std::string str);
bool is_integer(std::string str);

/*
 * Like tmpfname() from phpemu.c, but appends to
 * prefix the value returned by gethostid() in
 * an attempt to avoid conflicts on shared drives.
 *
 * Usage: new_tmpfname("/tmp/tmp-file-")
 * NOTE: the "XXXXXX" template required by tmpfname()
 *       should NOT be specified.
 */
std::string new_tmpfname(std::string prefix);

/* On Windows, replaces Windows-style slashes by Unix-style slashes */
std::string fix_slashes(std::string str);

#endif /* EZCSP_COMMON_H */
