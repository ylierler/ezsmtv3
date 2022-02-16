// by Marcello Balduccini [050709]
//
// Copyright (C) 2009-2021 Marcello Balduccini. All Rights Reserved.

#include "config.h"

#include <iostream>
#include <fstream>
#include <sstream>

#include <string>
#include <vector>

#include <string.h>

/* for ctime() and time() */
#include <time.h>

#ifdef HAVE_UNISTD_H
/* for unlink() */
#  include <unistd.h>
#endif

#include "phpemu.h"

#include "common.h"

using namespace std;
using namespace phpemu;

void rm_all_files(vector<string> all_files)
{	for (int i=0;i<(int)all_files.size();i++)
		unlink(all_files[i].c_str());
}

void open_err(string file) throw(runtime_error)
{	throw runtime_error("***Unable to open file "+file+". Aborting.");
}

void merge_files(string file1,string file2,string ofile) throw(runtime_error)
{	char b[FILECHUNK];

	ifstream fp;
	ofstream fpo;

	vector<string> flist;
	
	flist.push_back(file1);
	flist.push_back(file2);

	fpo.open(ofile.c_str(),ios::out | ios::trunc);
	if (fpo.fail())
	{	open_err(ofile);
		//rm_all_files(ALL_FILES);
		//exit(1);
	}

	for(int i=0;i<(int)flist.size();i++)
	{	
		fp.open(flist[i].c_str(),ios::in);
		if (fp.fail())
		{	open_err(flist[i]);
			//rm_all_files(ALL_FILES);
			//exit(1);
		}
		while(!fp.eof())
		{	fp.read(b,FILECHUNK);
			if (fp.gcount()>0)
				fpo.write(b,fp.gcount());
		}
		fp.close();
	}
	fpo.close();
}

// if convert_ASP_to_Prolog == true, then
// we turn " into ' because smodels uses " for strings and sicstus uses '
// MUST BE CHANGED DEPENDING ON ASP and CSP solver
//
// if file=="", input is from stdin
void myreadfile(string file,ostream *fpo,bool convert_ASP_to_Prolog) throw(runtime_error)
{	char b[FILECHUNK];

	istream *fp=NULL;

	if (file!="")
	{	fp=new ifstream(file.c_str());

		if (fp->fail())
		{	open_err(file);
			//rm_all_files(ALL_FILES);
			//exit(1);
		}
	}
	else
		fp=&cin;

	while(!fp->eof())
	{	fp->read(b,FILECHUNK);
		if (fp->gcount()>0)
		{	int i;

			if (convert_ASP_to_Prolog)
			{	for(i=0;i<fp->gcount();i++)
					if (b[i]=='\"')
						b[i]='\'';
			}

			fpo->write(b,fp->gcount());
		}
	}

	if (fp!=NULL && fp!=&cin)
		delete fp;
}

// if convert_ASP_to_Prolog == true, then
// we turn " into ' because smodels uses " for strings and sicstus uses '
// MUST BE CHANGED DEPENDING ON ASP and CSP solver
//
// if file=="", input is from stdin
void myreadfile_ASP_to_Prolog(string file,ostream *fpo) throw(runtime_error)
{	myreadfile(file,fpo,true);
}

string toString(vector<string> arr)
{	string s="";

	for(int i=0;i<(int)arr.size();i++)
		s=s+arr[i]+" ";
	
	return(s);
}

string toString(int i)
{	stringstream s;

	s << i;

	return(s.str());
}

bool startsWith(const string s,const string prefix)
{	if (s.substr(0,prefix.length())==prefix)
		return(true);
	return(false);
}

bool startsWith(const char *s,const char *prefix)
{	if (strncmp(s,prefix,strlen(prefix))==0)
		return(true);
	return(false);
}

bool my_egrep(string exp,string file,bool invert_match,bool display) throw(runtime_error)
{	bool found;
	string line;

	found=false;

	ifstream ifs(file.c_str());
	if (ifs.fail())
	{	open_err(file);
		//rm_all_files(ALL_FILES);
		//exit(1);
	}

	while(!ifs.eof())
	{	bool res;

		getline(ifs,line);
		if (ifs.fail()) break;

		res=preg_match(exp,line);
		
		if (invert_match)
			res=!res;

		if (res)
		{	found=true;

			if (display)
				cout << line << endl;
		}
	}

	ifs.close();

	return(found);
}

/* Like my_egrep, but no regular expressions, and
 * looking for a string at the beginning of the line.
 */
bool my_grep_startsWith(string prefix,string file,int max_occurrences,bool invert_match,bool display) throw(runtime_error)
{	bool found;
	string line;

	found=false;

	ifstream ifs(file.c_str());
	if (ifs.fail())
	{	open_err(file);
		//rm_all_files(ALL_FILES);
		//exit(1);
	}

	while(!ifs.eof())
	{	bool res;

		getline(ifs,line);
		if (ifs.fail()) break;

		res=startsWith(line,prefix);
		
		if (invert_match)
			res=!res;

		if (res)
		{	found=true;

			if (display)
				cout << line << endl;

			if (max_occurrences>0 && (max_occurrences--)==1)
				break;
		}
	}

	ifs.close();

	return(found);
}

/* Like my_egrep, but no regular expressions, and
 * looking for a string at the beginning of the *first* line.
 */
bool my_grep_startsWith_firstLine(string prefix,string file,bool invert_match,bool display) throw(runtime_error)
{	bool found;
	string line;

	found=false;

	ifstream ifs(file.c_str());
	if (ifs.fail())
	{	open_err(file);
		//rm_all_files(ALL_FILES);
		//exit(1);
	}

	if (ifs.eof())
	{	ifs.close();
		return(false);
	}

	bool res;

	getline(ifs,line);
	if (ifs.fail())
	{	ifs.close();
		return(false);
	}

	res=startsWith(line,prefix);
		
	if (invert_match)
		res=!res;

	if (res)
	{	found=true;

		if (display)
			cout << line << endl;
	}

	ifs.close();

	return(found);
}

string date(void)
{	string d;
	time_t t;

	time(&t);
	d=ctime(&t);

	d=trim(d);

	return(d);
}

bool is_floating_point(string str)
{	bool has_dot;
	const char *s;

	has_dot=false;
	s=str.c_str();
	if (*s=='-') s++;
	for(;*s!='\0';s++)
	{	if (*s=='.')
		{	if (has_dot) return(false);	// multiple dots
			has_dot=true;
		}
		else
		if (!isdigit(*s)) return(false);
	}

	return(has_dot);
}

bool is_integer(string str)
{	const char *s;

	s=str.c_str();
	if (*s=='-') s++;
	for(;*s!='\0';s++)
		if (!isdigit(*s)) return(false);

	return(true);
}

#ifndef HAVE_GETHOSTID
/* define gethostid() on systems that don't provide it */
#ifdef __MINGW32__
#include <winsock2.h>
#include <iphlpapi.h>
long gethostid(void)
{	unsigned long id;

	id=0;
	IP_ADAPTER_INFO AdapterInfo[1000];
	DWORD dwBufLen = sizeof(AdapterInfo);
	DWORD dwStatus = GetAdaptersInfo(AdapterInfo, &dwBufLen);
	if (dwStatus != ERROR_SUCCESS) return((long)id);

	PIP_ADAPTER_INFO pAdapterInfo = AdapterInfo;
 
//	printf("\tAdapter Name: \t%s\n", pAdapterInfo->AdapterName);
 
//	printf("\tAdapter Addr: \t");
	for (int i = 0; i < pAdapterInfo->AddressLength; i++)
	{	id = (id << 8) & ((unsigned long)pAdapterInfo->Address[i]);
	}
	return((long)id);
}
#else
long gethostid(void)
{	/* nothing we can do */
	return(0);
}
#endif
#endif

/*
 * Like tmpfname() from phpemu.c, but appends to
 * prefix the value returned by gethostid() in
 * an attempt to avoid conflicts on shared drives.
 *
 * Usage: new_tmpfname("/tmp/tmp-file-")
 * NOTE: the "XXXXXX" template required by tmpfname()
 *       should NOT be specified.
 */
string new_tmpfname(string prefix)
{	stringstream s;

	s << prefix << gethostid() << "-XXXXXX";

	return(tmpfname(s.str()));
}

/* On Windows, replaces Windows-style slashes by Unix-style slashes */
string fix_slashes(string str)
{
#ifdef __MINGW32__
	string oldStr="\\";
	string newStr="/";
	size_t pos = 0;
	while((pos = str.find(oldStr, pos)) != std::string::npos)
	{
		str.replace(pos, oldStr.length(), newStr);
		pos += newStr.length();
	}
#endif
	return(str);
}
