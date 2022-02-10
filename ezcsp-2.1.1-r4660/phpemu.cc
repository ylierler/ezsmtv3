// by Marcello Balduccini [050709]
//
// Copyright (C) 2009-2021 Marcello Balduccini. All Rights Reserved.

#include "config.h"

#include <stdio.h>
#include <stdlib.h>

/* for strdup() */
#include <string.h>

/* for ceilf() */
#include <math.h>

#if HAVE_SYS_WAIT_H
# include <sys/wait.h>
#else
#  ifndef WEXITSTATUS
#    define WEXITSTATUS(w)   (((w) >> 8) & 0xff)
#  endif
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
#include <signal.h>
#endif

#include <regex.h>

#include <iostream>
#include <fstream>

#include <string>
#include <vector>

#ifdef HAVE_UNISTD_H
/* for alarm() */
#  include <unistd.h>
#endif

#include "phpemu.h"

#include "common.h"

using namespace std;

namespace phpemu
{

/* local variables */
static bool cppsystem_debug=false;

#define ALARM_INTERVAL	1	/* secs */
static int cputime_limit=0;	/* secs */

static bool error_on_timeout=false;	/* whether the program should kill itself or just exit with no models on timeout */
/* */

/*
 * INTERNAL FUNCTION
 * =================
 *
 * Calls regcomp and regexec and returns the array of matches,
 * or NULL if there was no match. Output variable n_subs is set
 * to the number of entries in the array (notice that entry
 * number 0 is the input string that matched).
 * The array is as returned by regexec, and is allocated
 * by do_regexec() using calloc().
 * DON'T FORGET TO FREE THE ARRAY USING free()!!!
 *
 */
static regmatch_t *do_regexec(string preg,string str,int startindex,int &n_subs)
{	regex_t re;
	int res;
	regmatch_t *subs;

	res=regcomp(&re,preg.c_str(),REG_EXTENDED);
	/*
	 * [marcy 022610]
	 * WARNING: sometimes under OpenSuse the program
	 * hangs in regcomp(). I couldn't find any way to predict
	 * when that is going to happen.
	 */

	if (res!=0)
	{	/* compilation error */
		char s[1024];

		regerror(res,&re,s,1024);
		cerr << "regcomp error: " << s << endl;
		
		exit(1);
	}

	//cout << "# subs=" << re.re_nsub << endl;

	n_subs=re.re_nsub+1;
	subs=(regmatch_t *)calloc(n_subs,sizeof(regmatch_t));

	res=regexec(&re,&(str.c_str())[startindex],n_subs,subs,0);
	//cout << "regexec res=" << res << endl;

	regfree(&re);

	if (res!=0)	/* no match */
	{	free(subs);
		n_subs=0;
		return(NULL);
	}

	for(int i=0;i<n_subs;i++)
	{	subs[i].rm_so+=startindex;
		subs[i].rm_eo+=startindex;
	}

	return(subs);
}

bool preg_match(string preg,string str,int startindex,vector<string> &matches,int *endindex)
{	int i;
	int n_subs;
	regmatch_t *subs;

	subs=do_regexec(preg,str,startindex,n_subs);

	if (subs==NULL)
		return(false);

	for(i=0;i<n_subs;i++)
	{	if (subs[i].rm_so!=-1)
		{	matches.push_back(str.substr(
				subs[i].rm_so,subs[i].rm_eo-subs[i].rm_so));
		}
	}

	if (endindex!=NULL)
		*endindex=subs[0].rm_eo;

	free(subs);

	return(true);
}

bool preg_match(string preg,string str,int startindex,vector<string> &matches)
{	return(preg_match(preg,str,startindex,matches,NULL));
}

bool preg_match(string preg,string str,vector<string> &matches)
{	return(preg_match(preg,str,0,matches));
}

bool preg_match(string preg,string str)
{	vector<string> matches;

	return(preg_match(preg,str,matches));
}

bool preg_match_all(string preg,string str,vector< vector<string> > &matches)
{	int startindex;

	vector<string> submatches;

	startindex=0;
	while (startindex!=-1)
	{	
		if (!preg_match(preg,str,startindex,submatches,&startindex))
			startindex=-1;
		else
		{	matches.push_back(submatches);
			submatches.clear();
		}
	}

	return(matches.size()>0);
}


string preg_replace(string preg,string repl,string str)
{	int i;
	int n_subs;
	regmatch_t *subs;
	int startindex;

	startindex=0;
	while (startindex!=-1)
	{	subs=do_regexec(preg,str,startindex,n_subs);

		if (subs==NULL)
			return(str);

		/* prepare the replacement string */
		string r;
		r=repl;
		for(i=1;i<n_subs;i++)
		{	if (subs[i].rm_so!=-1)
			{	char k[3];

				k[0]='\\';
				k[1]='0'+i;
				k[2]=0;

				r=str_replace(k,
					      str.substr(subs[i].rm_so,subs[i].rm_eo-subs[i].rm_so),
					      r);
			}
		}

//cout << r << endl;

		if (subs[0].rm_so!=-1)
		{	str.replace(subs[0].rm_so,subs[0].rm_eo-subs[0].rm_so,r);
			startindex=subs[0].rm_so+r.length();
		}
		else
			startindex=-1;

//cout << "str=" << str << endl;
	}

	free(subs);

	return(str);
}

/* puts a backslash in front the characters:
 *           . \ + * ? [ ^ ] $ ( ) { } = ! < > | :
 */
string preg_quote(string str)
{	string chars="\\.+*?[^]$(){}=!<>|:";
	int i;

	/* IMPORTANT: the order in chars MATTERS.
	 * Because we add "\" in front of special
	 * chars, BUT we also replace "\" by "\\",
	 * "\" must be the first element of chars.
	 */
	for(i=0;i<(int)chars.length();i++)
	{	string c(1,chars[i]);
	
		str=str_replace(c,"\\"+c,str);
	}

	return(str);
}

string str_replace(string search,string replace,string subject)
{	string::size_type loc;

	loc=0;
	do
	{	loc = subject.find(search,loc);
			
		if (loc != string::npos)
		{	subject.replace(loc,search.length(),replace);
			
			loc+=replace.length();
		}

	} while (loc != string::npos);

	return(subject);
}

string rtrim(string str,string chars)
{	while(str.length()>0 && chars.find(str[str.length()-1])!=string::npos)
		str.erase(str.length()-1);

	return(str);
}

string ltrim(string str,string chars)
{	
	while(chars.find(str[0])!=string::npos)
		str.erase(0,1);

	return(str);
}

string trim(string str,string chars)
{	str=ltrim(str,chars);
	str=rtrim(str,chars);

	return(str);
}

void readfile(string file) throw(runtime_error)
{	char b[FILECHUNK];

	ifstream fp(file.c_str());
	if (fp.fail())
		throw runtime_error("***Unable to open file "+file+". Aborting.");

	while(!fp.eof())
	{	fp.read(b,FILECHUNK);
		if (fp.gcount()>0)
			cout.write(b,fp.gcount());
	}
	fp.close();
}

#if !defined(HAVE_MKSTEMP) && defined(HAVE_MKSTEMPS)
extern "C" int mkstemps (char *pattern, int suffix_len); 
#endif

timeout_error::timeout_error(const string& __arg)
: runtime_error(__arg) { }

string tmpfname(string tmpl)
{	char *s;
	string res;
	int h;
	FILE *fp;

	s=strdup(tmpl.c_str());

#ifdef HAVE_MKSTEMP
 	h=mkstemp(s);
#else
#  ifdef HAVE_MKSTEMPS
        h=mkstemps(s,0);
#  else
#    error "Either mkstemp() or mkstemps() must be available."
#  endif
#endif
	if (h<0)
	{	fprintf(stderr,"Unable to create temporary file from template \"%s\"...\n",tmpl.c_str());
		exit(1);
	}

	/* same as close(), but does not require include file unistd.h */
	fp=fdopen(h,"w");
	fclose(fp);

	res=s;

	free(s);

	return(res);
}

void set_cppsystem_debug(bool enabled)
{	cppsystem_debug=enabled;
}

int cppsystem(string cmd)
{	float d;

	return(cppsystem(cmd,d));
}

int cpprename(string old_file,string new_file)
{	return(rename(old_file.c_str(),new_file.c_str()));
}

int cppsystem(string cmd,float &duration)
{	int ret;

	float start_clock;

	if (cppsystem_debug)
		clog << "Exec: " << cmd << endl;

	start_clock=get_total_cpu();

	ret=system(cmd.c_str());

	duration=get_total_cpu()-start_clock;

	if (cppsystem_debug)
		clog << "Done: " << cmd << endl;

	return(WEXITSTATUS(ret));
}

#ifdef _WIN32
#include <sys/time.h>
#include <time.h>

timeval *init_cpu_timer(void)
{	static struct timeval tv;

	gettimeofday(&tv,NULL);

	return(&tv);
}

struct timeval *start_tv=init_cpu_timer();

int get_total_cpu_secs(void)
{	struct timeval tv;
	int total_sec,total_usec;

	gettimeofday(&tv,NULL);

	if (tv.tv_usec<start_tv->tv_usec)
	{	tv.tv_sec--;
		tv.tv_usec+=1000000;
	}
	total_usec=tv.tv_usec-start_tv->tv_usec;
	total_sec=tv.tv_sec-start_tv->tv_sec;

	return(total_sec+total_usec/1000000);
}

float get_total_cpu(void)
{	struct timeval tv;
	int total_sec,total_usec;

	gettimeofday(&tv,NULL);

	if (tv.tv_usec<start_tv->tv_usec)
	{	tv.tv_sec--;
		tv.tv_usec+=1000000;
	}
	total_usec=tv.tv_usec-start_tv->tv_usec;
	total_sec=tv.tv_sec-start_tv->tv_sec;

	return(((float)total_sec)+ceilf(((float)total_usec)/1000.0F)/1000.0F);
}
/*
int get_total_cpu_secs(void)
{	return ((double)clock() / CLOCKS_PER_SEC);
}
*/
#else
int get_total_cpu_secs(void)
{	struct rusage ru;
	int total_sec,total_usec;

	getrusage(RUSAGE_CHILDREN,&ru);
	total_sec=ru.ru_utime.tv_sec+ru.ru_stime.tv_sec;
	total_usec=ru.ru_utime.tv_usec+ru.ru_stime.tv_usec;

	getrusage(RUSAGE_SELF,&ru);
	total_sec+=ru.ru_utime.tv_sec+ru.ru_stime.tv_sec;
	total_usec+=ru.ru_utime.tv_usec+ru.ru_stime.tv_usec;

	return(total_sec+total_usec/1000000);
}

float get_total_cpu(void)
{	struct rusage ru;
	int total_sec,total_usec;

	getrusage(RUSAGE_CHILDREN,&ru);
	total_sec=ru.ru_utime.tv_sec+ru.ru_stime.tv_sec;
	total_usec=ru.ru_utime.tv_usec+ru.ru_stime.tv_usec;

	getrusage(RUSAGE_SELF,&ru);
	total_sec+=ru.ru_utime.tv_sec+ru.ru_stime.tv_sec;
	total_usec+=ru.ru_utime.tv_usec+ru.ru_stime.tv_usec;

	return(((float)total_sec)+ceilf(((float)total_usec)/1000.0F)/1000.0F);
}
#endif

void verify_cputime(string cmd="") throw(timeout_error)
{	if (cputime_limit>0 && get_total_cpu_secs() >= cputime_limit)
	{	if (error_on_timeout)
			//kill(getpid(),SIGXCPU);	// does not kill children and "|" pipes properly
			exit(2);
		else
			throw timeout_error((cmd=="") ? "***ezcsp: timeout":"***ezcsp: timeout while executing "+cmd);
	}
}

void alarm_function(int sig)
{

#ifdef _WIN32
	clog << "timeouts not supported under Windows!!" << endl;
#else
	//struct rusage ru;
	//int total_sec,total_usec;

//	printf("ALARM: total time: %d\n",get_total_cpu_secs());
	
	verify_cputime();

	alarm(ALARM_INTERVAL);
#endif
}

int get_cputime_left(void)
{	return(cputime_limit-get_total_cpu_secs());
}

/*
** Used to set the cputime limit.
** If the function is not invoked, the cputime
** is NOT LIMITED by default.
*/
void set_cputime_limit(int cputime_l)
{	cputime_limit=cputime_l;

#ifdef _WIN32
	clog << "timeouts not supported under Windows!!" << endl;
#else
	if (cputime_limit>0)
	{	signal(SIGALRM,alarm_function);
		alarm(ALARM_INTERVAL);
	}
#endif
}

/*
** Used to set whether we must give error on timeout.
*/
void set_error_on_timeout(bool error_on_timeout_l)
{	error_on_timeout=error_on_timeout_l;
}

int timed_cppsystem(std::string cmd) throw(timeout_error)
{	float d;

	return(timed_cppsystem(cmd,d));
}

int timed_cppsystem(std::string cmd,float &duration) throw(timeout_error)
{	string str;

	int ret;

	float start_clock;

	if (cputime_limit>0)
	{	verify_cputime();

		str=((string)"ulimit -t ") + 
		    toString(get_cputime_left()) +
		    " ; " +
		    cmd;
	}
	else
		str=cmd;


	if (cppsystem_debug)
		clog << "Exec: " << cmd << endl;

	start_clock=get_total_cpu();

	ret=system(str.c_str());

	duration=get_total_cpu()-start_clock;

	if (cppsystem_debug)
		clog << "Done: " << cmd << endl;

#ifndef _WIN32
	if (WIFSIGNALED(ret))	/* child terminated abnormally */
		kill(getpid(),WTERMSIG(ret));
	else
	if (cputime_limit>0)	/* this second cputime test allows us to catch an exceeded limit */
		verify_cputime(cmd);	/* without waiting for another call to timed_system(). */
#endif

	return(WEXITSTATUS(ret));
}

}
