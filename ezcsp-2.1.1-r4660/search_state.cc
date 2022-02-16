#include "config.h"

#include <fstream>
#include <iostream>

#include <string>
#include <vector>

/* for exit(), atoi() */
#include <stdlib.h>

#include "common.h"

#include "phpemu.h"

#include "search_state.h"

using namespace std;
using namespace phpemu;

const string state_delim="+-+-+-+-";


void load_search_state_asp(string SEARCH_STATE,string PREV_ASP_MODELS)
{	fstream fp,fpo;

	fp.open(SEARCH_STATE.c_str(),ios::in);
	if (fp.fail())
		open_err(SEARCH_STATE);

	fpo.open(PREV_ASP_MODELS.c_str(),ios::out | ios::trunc);
	if (fpo.fail())
		open_err(PREV_ASP_MODELS);

	while(!fp.eof())
	{	string line;

		getline(fp,line);
		if (fp.fail()) break;

		if (line==state_delim) break;

		fpo << line << endl;
	}
	fpo.close();

	fp.close();
}

void append_search_state_csp(string SEARCH_STATE,string CP_SOLS)
{	fstream fp,fpo;
	bool in_csp_section;

	fp.open(SEARCH_STATE.c_str(),ios::in);
	if (fp.fail())
		open_err(SEARCH_STATE);

	fpo.open(CP_SOLS.c_str(),ios::out | ios::app);
	if (fpo.fail())
		open_err(CP_SOLS);

	in_csp_section=false;
	while(!fp.eof())
	{	string line;

		getline(fp,line);
		if (fp.fail()) break;

		if (in_csp_section)
			fpo << line << endl;
		else
		if (line==state_delim)
			in_csp_section=true;

	}
	fpo.close();

	fp.close();
}

void store_search_state(string SEARCH_STATE,string PREV_ASP_MODELS,string CP_SOLS,bool csp_state_valid)
{	fstream fp,fpo;

	fpo.open(SEARCH_STATE.c_str(),ios::out | ios::trunc);
	if (fpo.fail())
		open_err(SEARCH_STATE);

	myreadfile(PREV_ASP_MODELS,&fpo);

	fpo << state_delim << endl;

	if (csp_state_valid)
	{	fp.open(CP_SOLS.c_str(),ios::in);
		if (fp.fail())
			open_err(CP_SOLS);

		bool in_csp_solutions=false;
		while(!fp.eof())
		{	string line;

			getline(fp,line);
			if (fp.fail()) break;

			if (!in_csp_solutions && startsWith(line,"skip_solution(["))
				in_csp_solutions=true;

			if (in_csp_solutions)
				fpo << line << endl;
		}
		fp.close();
	}

	fpo.close();
}
