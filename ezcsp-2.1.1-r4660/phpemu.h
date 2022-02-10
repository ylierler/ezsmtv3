#ifndef EZCSP_PHPEMU_H
#define EZCSP_PHPEMU_H

// by Marcello Balduccini [050709]
//
// Copyright (C) 2009-2021 Marcello Balduccini. All Rights Reserved.

#include <string>
#include <vector>

#include <exception>
#include <stdexcept>

#include "defs.h"

//using namespace std;

namespace phpemu
{
/*
 * Implementation of PHP's preg_match(), preg_replace(), 
 * preg_quote(), str_replace(), rtrim(), ltrim(), trim(),
 * readfile().
 */

/*
 * IMPORTANT: in the functions below, the regular expressions
 * are specified WITHOUT the "/" prefix and suffix.
 */
bool preg_match(std::string preg,std::string str,int startindex,std::vector<std::string> &matches,int *endindex);
bool preg_match(std::string preg,std::string str,int startindex,std::vector<std::string> &matches);
bool preg_match(std::string preg,std::string str,std::vector<std::string> &matches);
bool preg_match(std::string preg,std::string str);
bool preg_match_all(std::string preg,std::string str,std::vector< std::vector<std::string> > &matches);
std::string preg_replace(std::string preg,std::string repl,std::string str);
/* puts a backslash in front the characters:
 *           . \ + * ? [ ^ ] $ ( ) { } = ! < > | :
 */
std::string preg_quote(std::string str);
std::string str_replace(std::string search,std::string replace,std::string subject);
std::string rtrim(std::string str,std::string chars=" \t\n\r\x0B");
std::string ltrim(std::string str,std::string chars=" \t\n\r\x0B");
std::string trim(std::string str,std::string chars=" \t\n\r\x0B");
void readfile(std::string file) throw(std::runtime_error);


/*
 * Misc functions
 */

class timeout_error : public std::runtime_error
{
public:
	explicit timeout_error(const std::string & __arg);
};

int cpprename(std::string old_file,std::string new_file);

std::string tmpfname(std::string tmpl);
void set_cppsystem_debug(bool enabled);
/* Duration of the execution of cmd is stored in variable "duration", if provided.*/
int cppsystem(std::string cmd);
int cppsystem(std::string cmd,float &duration);
/*
** Used to set the cputime limit.
** If the function is not invoked, the cputime
** is NOT LIMITED by default.
*/
void set_cputime_limit(int cputime_l);
/*
** Used to set whether we must give error on timeout.
*/
void set_error_on_timeout(bool error_on_timeout_l);
int get_cputime_left(void);
/* Get total cpu time used so far in seconds plus 3 decimal digits */
float get_total_cpu(void);
/*
 * Runs cmd with instructions to abort it if we reach the overall timeout.
 * Duration of the execution of cmd is stored in variable "duration", if provided.
 */
int timed_cppsystem(std::string cmd) throw(timeout_error);
int timed_cppsystem(std::string cmd,float &duration) throw(timeout_error);
}

#endif /* EZCSP_PHPEMU_H */
