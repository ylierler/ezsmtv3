// by Marcello Balduccini [050709]
// Copyright (C) 2009-2021 Marcello Balduccini. All Rights Reserved.
//
// Translates a set of literals containing a CSP definition
// into the CLP encoding the same CSP.
// Each literal must be ground and followed by a "." (e.g. "mkatoms -a" format).
// Double-quotes can be used for quoting.
//
// Usage: translate <file1> [<file2>...]
//    or: translate    (with no arguments) to use standard input
//

#include "config.h"

#include <iostream>
#include <fstream>

#include <string>
#include <vector>

/* for exit() */
#include <stdlib.h>

#include "phpemu.h"

#include "common.h"

#include "search_state.h"

#include "cmdline_params.h"

#include "translate.h"

using namespace std;
using namespace phpemu;

/* result: 1 -> error; 0 -> success */
//int translate(string translator,string CPSOLVER,int cpsolver_type,vector<string> FILES,bool quick_trans,bool relaxed_labeling,bool *append_footer,string ofile="") throw(runtime_error)
int translate(string translator,string CPSOLVER,int cpsolver_type,vector<string> FILES,cmdline_params p,bool *append_footer,string ofile="") throw(runtime_error)
{	ostream *pfx=NULL;
	fstream fp;

	vector<string> ALL_FILES;

	try
	{	if (ofile!="")
		{	pfx=new ofstream(ofile.c_str());
			if (pfx->fail())
			{	open_err(ofile);
				//rm_all_files(ALL_FILES);
				//exit(1);
			}
		}
		else
			pfx=&cout;

		string TDIR;
#ifdef __MINGW32__
		char *tmpdir=getenv("TEMP");
		TDIR=tmpdir;
		if (tmpdir==NULL)
#endif
		TDIR="/tmp";
		//
		string TFILE1=new_tmpfname(TDIR+"/trn-1-");
		string PL_TRANS=new_tmpfname(TDIR+"/trn-2-");
		string TFILE2=new_tmpfname(TDIR+"/trn-3-");
		string PL_TRANS_ERR=new_tmpfname(TDIR+"/trn-4-");
		//
		ALL_FILES.push_back(TFILE1);
		ALL_FILES.push_back(PL_TRANS);
		ALL_FILES.push_back(TFILE2);
		ALL_FILES.push_back(PL_TRANS_ERR);


		fp.open(TFILE1.c_str(),ios::out | ios::trunc);
		if (fp.fail())
		{	open_err(TFILE1);
			//rm_all_files(ALL_FILES);
			//exit(1);
		}

		// we turn " into ' because smodels uses " for strings and sicstus uses '
		// MUST BE CHANGED DEPENDING ON ASP and CSP solver
		for(int i=0;i<(int)FILES.size();i++)
		{	if (FILES[i]=="-")
				myreadfile_ASP_to_Prolog("",&fp);
			else
				myreadfile_ASP_to_Prolog(FILES[i],&fp);
		}

		if (p.quick_translation)
		{	struct
			{	int cpsolver_type;
				char *opt;
				bool append_footer;
			}
			cpsolver_opts[]=
			{	{ CPSOLVER_SICSTUS3, (char *)"-3", true },
				{ CPSOLVER_SICSTUS4, (char *)"-4", true },
				{ CPSOLVER_BPROLOG,  (char *)"-bp", true },
				{ CPSOLVER_SWIPROLOG,  (char *)"-swi", true },
				{ CPSOLVER_GAMS,  (char *)"-gams", false },
				{ CPSOLVER_MINIZINC,  (char *)"-minizinc", false },
				{ CPSOLVER_GUROBI,  (char *)"-gurobi", false },
				{ -1, NULL }
			};
			int i;
			string cpsolver_opt="";
			int ret;

			fp.close();

			for(i=0;cpsolver_opt=="" && cpsolver_opts[i].cpsolver_type!=-1;i++)
			{	if (cpsolver_opts[i].cpsolver_type==cpsolver_type)
				{	cpsolver_opt=cpsolver_opts[i].opt;
					if (append_footer)
						*append_footer=cpsolver_opts[i].append_footer;
				}
			}
			if (cpsolver_opt=="")
				cpsolver_opt="-4";

			/* call translate2 */
			ret=cppsystem(translator+" "+
				cpsolver_opt+
				(p.relaxed_labeling ? " --relaxed-labeling":"")+
				(p.allow_unsupported ? " --allow-unsupported":"")+
				" \""+TFILE1+"\" > \""+PL_TRANS+"\" 2>\""+PL_TRANS_ERR+"\""); // /dev/null
			if (ret!=0)
			{	// then there was some execution error
				cerr << "Error while executing " << translator << "! (code=" << ret << "):" << endl;
				myreadfile(PL_TRANS,&cerr);
				myreadfile(PL_TRANS_ERR,&cerr);
#ifndef COMPILE_TRANSLATE_MAIN
				extern vector<string> ALL_FILES;
				rm_all_files(ALL_FILES);
#endif
				exit(1);
			}

			// remove the verbose header of the Prolog interpreter
			fp.open(PL_TRANS.c_str(),ios::in);

			if (fp.fail())
			{	open_err(PL_TRANS);
				//rm_all_files(ALL_FILES);
				//exit(1);
			}
		}
		else
		{	extern char *trans_pl;
			fp << trans_pl;

			extern char *exec_pl;
			fp << exec_pl;

			extern char *dors_pl;
			fp << dors_pl;

			fp << "?- translate_batch." << endl;

			fp.close();

			//cppsystem(CPSOLVER+" -l \""+TFILE1+"\" --goal 'translate_batch.' > \""+PL_TRANS+"\" 2>\""+PL_TRANS_ERR+"\""); // /dev/null
			cppsystem(CPSOLVER+" -l \""+TFILE1+"\" > \""+PL_TRANS+"\" 2>\""+PL_TRANS_ERR+"\""); // /dev/null

			if (my_egrep("^\\+\\+failed",PL_TRANS,false,false))
			{	cppsystem("grep '^\\*\\*\\*' "+PL_TRANS);
				myreadfile(PL_TRANS,pfx);
				myreadfile(PL_TRANS_ERR,pfx);
				throw runtime_error("");
			}

			// remove the verbose header of the Prolog interpreter
			fp.open(PL_TRANS.c_str(),ios::in);

			if (fp.fail())
			{	open_err(PL_TRANS);
				//rm_all_files(ALL_FILES);
				//exit(1);
			}
			while(!fp.eof())
			{	string line;

				vector<string> matches;

				getline(fp,line);
				if (fp.fail()) break;

				line=trim(line);

				if (line=="=-=-=-=-=") break;
			}
		}
		// now output the rest of the file (we read large chunks for efficiency)
		while(!fp.eof())
		{	char b[FILECHUNK];
			fp.read(b,FILECHUNK);
			if (fp.gcount()>0)
				pfx->write(b,fp.gcount());
		}
		fp.close();
	}
	catch(runtime_error& e)
	{	cerr << e.what() << endl;
		rm_all_files(ALL_FILES);

		if (pfx!=NULL && pfx!=&cout) delete pfx;

		return(1);
	}


	rm_all_files(ALL_FILES);
	
	if (pfx!=&cout) delete pfx;
	
	return(0);
}

//int translate(string translator,string CPSOLVER,int cpsolver_type,string FILE,bool quick_trans,bool relaxed_labeling,bool allow_unsupported,bool *append_footer,string ofile="") throw(runtime_error)
int translate(string translator,string CPSOLVER,int cpsolver_type,string FILE,cmdline_params p,bool *append_footer,string ofile="") throw(runtime_error)
{	vector<string> FILES;

	FILES.push_back(FILE);
	
	return(translate(translator,CPSOLVER,cpsolver_type,FILES,p,append_footer,ofile));
}

void csp_exec_cmds_nonCLP(cmdline_params p,fstream *fp,string DEFPART,string CP_SOLS)
{	cerr << "***WARNING: multiple CP solutions supported only with CLP" << endl;
	cerr << "***WARNING: defined part supported only with CLP" << endl;
}

void csp_exec_cmds_prolog(cmdline_params p,fstream *fp,string DEFPART,string CP_SOLS)
{	string consult="consult";
	if (p.CPSOLVER_TYPE==CPSOLVER_BPROLOG && !p.bprolog_no_compile)
	{	// use compile-and-load (cl/1) to
		// prevent B-Prolog from generating
		// a temp file "__tmp.out" in the
		// current directory when it
		// encounters a table directive.
		// Such a file may cause conflicts
		// when multiple instances of
		// ezcsp are being run.
		consult="cl";
	}
	/* Load the defined part */
	(*fp) << ":- "<< consult << "('" << fix_slashes(DEFPART) << "')." << endl;

	/* Ensure the list of previously-found solutions is loaded before specifying the goal */
	(*fp) << ":- " << consult << "('" << fix_slashes(CP_SOLS) << "')." << endl;

	/* Specify the goal in a way that is compatible with Sicstus 3.8.x */
	string sicstus_goal;
	string solv_name;
	switch(p.CPSOLVER_TYPE)
	{	case CPSOLVER_SICSTUS3:
		case CPSOLVER_SICSTUS4:
			solv_name="sicstus";
			break;
		case CPSOLVER_SWIPROLOG:
			solv_name="swiprolog";
			break;
		case CPSOLVER_BPROLOG:
			solv_name="bprolog";
		break;
	}
	if (p.cputime_limit>0)
		sicstus_goal=((string)"batch_to(") + solv_name + ", " + toString(get_cputime_left()*1000) + ").";
	else
		sicstus_goal=((string)"batch(")+solv_name+").";
	(*fp) << "?- " << sicstus_goal << endl;
}

/*
 * Returns false if the translation failed. True otherwise.
 */
bool translate_to_csp(cmdline_params p,string ASP_MOD,string TFILE1,string DEFPART,string CP_SOLS,string PL_TRANS)
{	int ret;
	fstream fp;
	bool append_footer;

	if (p.separate_translation)
	{	if (p.DEBUG_TIMES)
			clog << "Before translation: " << date() << endl;

		append_footer=true;	/* by default, we append the Prolog footer to the translation.
					 * translate() will tell us if we need to do differently. */
		//ret=translate(p.TRANSLATOR,p.CPSOLVER,p.CPSOLVER_TYPE,TFILE1,p.quick_translation,p.relaxed_labeling,p.allow_unsupported,&append_footer,PL_TRANS);
		ret=translate(p.TRANSLATOR,p.CPSOLVER,p.CPSOLVER_TYPE,TFILE1,p,&append_footer,PL_TRANS);

		if (p.DEBUG_TIMES)
			clog << "After translation: " << date() << endl;

		if (ret==1)
		{	cerr << "***Error while translating the CSP definition:" << endl;
			myreadfile(TFILE1,&cerr);
			cerr << "***<---- Program end." << endl;
			cerr << "***Result was:" << endl;
			myreadfile(PL_TRANS,&cerr);
			cerr << "***<---- Result end." << endl;
			return(false);
		}


		fp.open(PL_TRANS.c_str(),ios::out | ios::app);
		if (fp.fail())
		{	open_err(PL_TRANS);
			//rm_all_files(ALL_FILES);
			//exit(1);
		}

		if (append_footer)
		{	extern char *exec_pl;
			fp << exec_pl;
/*
			extern char *dors_pl;
			fp << dors_pl;
*/
		}

		fp.close();

//		cppsystem("cp "+PL_TRANS+" zzz");
	}
	else
	{	fp.open(PL_TRANS.c_str(),ios::out | ios::trunc);
		if (fp.fail())
			open_err(PL_TRANS);

		myreadfile_ASP_to_Prolog(TFILE1,&fp);

		extern char *trans_pl;
		fp << trans_pl;

		extern char *exec_pl;
		fp << exec_pl;

		extern char *dors_pl;
		fp << dors_pl;

		fp.close();
	}

	/* Pass info regarding the options to load and save csp choices. */
	fp.open(PL_TRANS.c_str(),ios::out | ios::app);
	if (fp.fail())
	{	open_err(PL_TRANS);
		//rm_all_files(ALL_FILES);
		//exit(1);
	}

	if (append_footer)
	{	if (p.load_csp_choices)
		{	fp << "dors_prolog_stack_load(yes)." << endl;
			fp << "dors_prolog_stack_load(file('"<< p.CSP_CHOICES_IN << "'))." << endl;
		}
		else
			fp << "dors_prolog_stack_load(no)." << endl;
		if (p.save_csp_choices || p.append_csp_choices)
		{	fp << "dors_prolog_stack_save(yes)." << endl;
			fp << "dors_prolog_stack_save(file('"<< p.CSP_CHOICES_OUT << "'))." << endl;
			fp << "dors_prolog_stack_save_append(";
			if (p.append_csp_choices)
				fp << "yes";
			else
				fp << "no";
			fp << ")." << endl;
			fp << ":- fdbg_on([no_constraint_hook,labeling_hook(my_fdbg_label_show)])." << endl;
		}
		else
			fp << "dors_prolog_stack_save(no)." << endl;
		fp << "dors_prolog_stack_type(";
		if (p.merged_csp_choices)
			fp << "merged";
		else
			fp << "single";
		fp << ")." << endl;
	}

	if (p.CPSOLVER_TYPE==CPSOLVER_GAMS || p.CPSOLVER_TYPE==CPSOLVER_MINIZINC || p.CPSOLVER_TYPE==CPSOLVER_GUROBI)
		csp_exec_cmds_nonCLP(p,&fp,DEFPART,CP_SOLS);
	else
		csp_exec_cmds_prolog(p,&fp,DEFPART,CP_SOLS);

	if (0==1)
	{	string consult="consult";
		if (p.CPSOLVER_TYPE==CPSOLVER_BPROLOG && !p.bprolog_no_compile)
		{	// use compile-and-load (cl/1) to
			// prevent B-Prolog from generating
			// a temp file "__tmp.out" in the
			// current directory when it
			// encounters a table directive.
			// Such a file may cause conflicts
			// when multiple instances of
			// ezcsp are being run.
			consult="cl";
		}
		/* Load the defined part */
		fp << ":- "<< consult << "('" << fix_slashes(DEFPART) << "')." << endl;

		/* Ensure the list of previously-found solutions is loaded before specifying the goal */
		fp << ":- " << consult << "('" << fix_slashes(CP_SOLS) << "')." << endl;

		/* Specify the goal in a way that is compatible with Sicstus 3.8.x */
		string sicstus_goal;
		string solv_name;
		switch(p.CPSOLVER_TYPE)
		{	case CPSOLVER_SICSTUS3:
			case CPSOLVER_SICSTUS4:
				solv_name="sicstus";
				break;
			case CPSOLVER_SWIPROLOG:
				solv_name="swiprolog";
				break;
			case CPSOLVER_BPROLOG:
				solv_name="bprolog";
			break;
		}
		if (p.cputime_limit>0)
			sicstus_goal=((string)"batch_to(") + solv_name + ", " + toString(get_cputime_left()*1000) + ").";
		else
			sicstus_goal=((string)"batch(")+solv_name+").";
		fp << "?- " << sicstus_goal << endl;
	}

	fp.close();

	if (p.load_search_state)
	{	append_search_state_csp(p.SEARCH_STATE_IN,CP_SOLS);
		p.load_search_state=false;	// we have loaded all that there was to load
	}
	
	return(true);
}


#ifdef COMPILE_TRANSLATE_MAIN
/* for dirname() */
#include <libgen.h>

int main(int argc,char *argv[])
{	vector<string> FILES;
	cmdline_params p;

	for(int i=1;i<argc;i++)
		FILES.push_back(argv[i]);

	if (FILES.size()==0)
		FILES.push_back("-");

	p.quick_translation=false;
	p.relaxed_labeling=false;
	p.allow_unsupported=false;
	int ret=translate("./translate2","sicstus",CPSOLVER_SICSTUS4,FILES,p,NULL);

	exit(ret);
}

#endif /* COMPILE_TRANSLATE_MAIN */
