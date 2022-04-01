#include "config.h"

#include <fstream>
#include <iostream>

#include <string>
#include <vector>

/* for exit(), atoi() */
#include <stdlib.h>

#include <string.h>

#include "common.h"

#include "phpemu.h"

#include "asp_solver.h"

#ifdef HAVE_CMODELS
/* for cmodels */
#include "ctable.h"
#endif /* HAVE_CMODELS */

/* define for cmodels >= 3.83 */
#define USE_TRUE_EXTERNAL


using namespace std;
using namespace phpemu;


class lpatom /* used by retrieve_id */
{
public:
	int index;
	const char *name;

	lpatom(const char *_name=NULL,int _index=0)
	{	static const char *empty="";

		if (_name==NULL)
			name=empty;
		else
			name=strdup(_name);

		index=_index;
	}

	int compute_hash_value(void)
	{	return(compute_hash_value(name));
	}
	
	static int compute_hash_value(const char *s)
	{	int h,i;

#define HASH_MOD 1000

		for(h=i=0;s[i]!=0;h=(h+s[i++]) % HASH_MOD);

		return(h);
	}
};

vector<lpatom *> names;
vector<vector <lpatom *> > names_hash;

void add_name(const string name,int id)
{	lpatom *l=new lpatom(name.c_str(),id);
	int v=l->compute_hash_value();

	if (((int)names.size())<l->index+1)
		names.resize(l->index+1);
	names[l->index]=l;

	if (((int)names_hash.size())<=v)
		names_hash.resize(v+1);
	names_hash[v].push_back(l);
}

void add_name(const string line)
{	int i;

	for(i=0;i<(int)line.length() && line[i]!=' ';i++);
	if (i<(int)line.length())
		add_name(trim(line.substr(i+1)),atoi(trim(line.substr(0,i)).c_str()));
}

void ensure_names_loaded(string PARSED)
{	string line;

	if ((int)names.size()==0)
	{	

#define BUFS 102400
		char buf[BUFS+1];
	
		ifstream fp_parsed(PARSED.c_str());
		if (fp_parsed.fail())
		{	open_err(PARSED);
			//rm_all_files(ALL_FILES);
			//exit(1);
		}
		
		int off,n;

		/* skip the 1st section (rules) */
		bool found_section_end=false;
		bool at_line_start=true;
		off=0;
		n=0;
		while(!found_section_end && !fp_parsed.eof())
		{	int i;

			fp_parsed.read(&buf[off], BUFS-off);
			n=fp_parsed.gcount();
			n+=off;

			for(i=0;i<n-1;i++)
			{	
				if (((i==0 && at_line_start) || (i>0 && buf[i-1]=='\n')) &&
				    (buf[i]=='0') &&
				    (buf[i+1]=='\n'))
				{	i+=2;
					found_section_end=true;
					break;
				}
			}

			if (i>0)
				at_line_start=(buf[i-1]=='\n');

			if (i<n)
			{	// Replacement for
				//	memcpy(buf,&buf[i],n-i)
				// that works for overlapping areas
				// and does not involve extra storage
				// like memmove().
				for(int j=0;j<n-i;j++)
					buf[j]=buf[j+i];
				off=n-i;
			}
			else
				off=0;
		}

		bool first_round=(off>0);
		while(first_round || !fp_parsed.eof())
		{	int i,st;

			if (first_round)
				n=off;
			else
			{	fp_parsed.read(&buf[off], BUFS-off);
				n=fp_parsed.gcount();
				n+=off;
			}
			first_round=false;

			for(st=i=0;i<n-1;i++)
			{	if (buf[i]=='\n')
				{	buf[i]=0;
					if (strcmp(&buf[st],"0")==0)
					{	off=0;
						break;	// end of section
					}

					add_name(&buf[st]);
					//add_name(trim(&buf[st]));
					st=i+1;
				}
			}
			if (st<n)
			{	// Replacement for
				//	memcpy(buf,&buf[st],n-st)
				// that works for overlapping areas
				// and does not involve extra storage
				// like memmove().
				for(int j=0;j<n-st;j++)
					buf[j]=buf[j+st];
				off=n-st;
			}
			else
				off=0;
		}
		if (n<=0 && off>0)
		{	buf[off]=0;
			if (strcmp(buf,"0")!=0)
			add_name(buf);
			//add_name(trim(buf));
		}

		fp_parsed.close();
	}
}

void load_names_from_symbolTable(const char **symbolTable,int symbolTableEntries)
{	for(int i=0;i<symbolTableEntries;i++)
		if (symbolTable[i]!=NULL)
			add_name(symbolTable[i],i);
}

int retrieve_id(const string PARSED,string atom) throw(runtime_error)
{	ensure_names_loaded(PARSED);

	int v=lpatom::compute_hash_value(atom.c_str());
	
	if (((int)names_hash.size())<=v) return(-1);

	for(int i=0;i<(int)names_hash[v].size();i++)
	{	if (names_hash[v][i]!=NULL && names_hash[v][i]->name==atom)
			return(names_hash[v][i]->index);
	}

	return(-1);
}

const char *retrieve_name(const string PARSED,int id) throw(runtime_error)
{	static const char *empty="";

	ensure_names_loaded(PARSED);

	if (id<(int)names.size() && names[id]!=NULL)
		return(names[id]->name);

	return(empty);
}

int output_like_mkatoms(cmdline_params p,const string PARSED,int *cmodels_assignments,int num_assignments,const string OUTPUT_FILE)
{	fstream fp;
	int i;
	int count;

	fp.open(OUTPUT_FILE.c_str(),ios::out | ios::trunc);
	if (fp.fail())
	{	open_err(OUTPUT_FILE);
	}
	
	count=0;
	for(i=0;i<num_assignments;i++)
	{	if (p.DEBUG)
		{	cerr << "assignment: " << cmodels_assignments[i] << endl;
			cerr << "  abs(lit)=" << retrieve_name(PARSED,cmodels_assignments[i]<0 ? -cmodels_assignments[i]:cmodels_assignments[i]) << endl;
		}

		if (cmodels_assignments[i]>0)	/* >0 means positively in (as opposed to "not l" in the partial interpretation) */
		{	const char *name=retrieve_name(PARSED,cmodels_assignments[i]);
			if (name[0]!=0)	/* filter out hidden atoms such as true and false */
			{	count++;
				fp << name << "." << endl;
			}
		}
	}
	fp.close();

	return(count);
}

#ifdef HAVE_CMODELS
/* cmodels-related */
Ctable ctable;
bool Atom::change = false;
bool Atom::conflict = false;
bool program_loaded=false;
int *answerset_lits;
int num_atoms;
bool program_is_already_inconsistent=false;
/* END of cmodels-related */

bool all_models_found=false;

static int cmpintp(const void *p1, const void *p2)
{	int i1,i2;

	i1=*(int const *)p1;
	i2=*(int const *)p2;

	return(i1-i2);
}

void markCSPAtoms(cmdline_params p,const string PARSED) throw(runtime_error)
{	int *cspatoms,n_cspatoms;
	int i;
	bool is_relevant_atom(const char *n);

	ensure_names_loaded(PARSED);

	cspatoms=new int[names.size()];

#ifdef USE_TRUE_EXTERNAL
	bool *trueExternal=new bool[names.size()];
#endif

	n_cspatoms=0;
	for(i=0;i<(int)names.size();i++)
	{	const char *name;

		name=retrieve_name(PARSED,i);
		if (startsWith(name,PL_RELATION_PREFIX))
		{	cerr << "Error: '"PL_RELATION_PREFIX"'-prefixed relations are not compatible with cmodels-feedback mode." << endl;
			exit(1);
		}

#ifdef USE_TRUE_EXTERNAL
		cspatoms[i]=i;
		trueExternal[i]=is_relevant_atom(name);
		n_cspatoms++;
		if (p.DEBUG)
		{	if (is_relevant_atom(name))
				cerr << "marking csp atom #" << i << " name=" << name << endl;
			else
				cerr << "non-external atom #" << i << " name=" << name << endl;
		}
#else
		if (is_relevant_atom(name))
		{	if (p.DEBUG) cerr << "marking csp atom #" << i << " name=" << name << endl;
			cspatoms[n_cspatoms++]=i;
		}
#endif
	}

	qsort(cspatoms,n_cspatoms,sizeof(int),cmpintp);

#ifdef USE_TRUE_EXTERNAL
	ctable.markExternallyConstrainedAtoms(cspatoms,n_cspatoms,trueExternal);
#else
	ctable.markExternallyConstrainedAtoms(cspatoms,n_cspatoms);
#endif

	delete cspatoms;
}

testPartialSolutionInfo *tpsi_=NULL;

void asp_solver_set_tpsInfo(testPartialSolutionInfo *tpsi)
{	tpsi_=tpsi;
}

/*
 * Returns true if a model was found (and stored in ASP_MOD) and false otherwise.
 */
bool call_cmodels(cmdline_params p,string INPUT,string ASP_MOD,bool *pure_asp,bool forced_pure_asp,int MODEL_NUM)
{	fstream fp;
	bool skip_solve;
	string TFILE1;

	skip_solve=false;
	num_atoms=-1;

	if (!program_loaded)
	{	FILE *fp;

		if (!p.QUIET)
			clog << "using cmodels version " << ctable.cmodels_version() << endl;

		fp=fopen(INPUT.c_str(),"r");
		if (fp==NULL)
			return(false);
		ctable.read(fp);

		fclose(fp);

		/* MINISAT1 is *required* for interactive feedback */
		//ctable.setSolver(MINISAT);
		ctable.setSolver(MINISAT1);
		// or ctable.setSolver(MINISAT1);
		// or ctable.setSolver(MINISAT2);

		if (p.cmodels_lib_options!="")
			ctable.setExecutionArgs((char *)p.cmodels_lib_options.c_str());

		const char **symbolTable;
		int symbolTableEntries;

		answerset_lits=new int[ctable.getNumberGroundedAtoms()];
		ctable.Initialize(answerset_lits,num_atoms,symbolTable,symbolTableEntries);

		load_names_from_symbolTable(symbolTable,symbolTableEntries);

		program_loaded=true;

		all_models_found=false;

		if (num_atoms>=0 || num_atoms==-1 /* inconsistent */)
		{	skip_solve=true;	// Initialize already found a unique model
			all_models_found=true;	// All models have been found
		}
		else
		if (p.use_cmodels_feedback)
		{	/* perform some solver initialization */
			markCSPAtoms(p,INPUT);
			ctable.setTestPartialSolutionInfo(tpsi_);
		}
	}

	if (program_is_already_inconsistent)	/* latest call to addDenial() determined inconsistency */
	{	skip_solve=true;
		num_atoms=-1;
		all_models_found=true;	// All models have been found
	}

	if (!skip_solve && !all_models_found)
		ctable.Solve(answerset_lits, num_atoms);

	fp.open(ASP_MOD.c_str(),ios::out | ios::trunc);
	if (fp.fail())
	{	open_err(ASP_MOD);
		//rm_all_files(ALL_FILES);
		//exit(1);
	}

	if (num_atoms<0)
	{	fp << "False" << endl;
		
		fp.close();

		*pure_asp=true;
		if (!forced_pure_asp)	/* if we *already* know that it is pure asp, we take shortcuts */
		{	TFILE1=INPUT;	// now we use the input as temporary output file [DANGER!!!!!]
			timed_cppsystem("mkatoms -a < \""+ASP_MOD+"\" > \""+TFILE1+"\"");
		}

		return(false);
	}

	fp << "Answer: " << MODEL_NUM << endl;
	fp << "Stable Model: ";

clog << "before pure-check: " << get_total_cpu() << endl;
	*pure_asp=true;
	for(int i=0;i<num_atoms;i++)
	{	//if (answerset_lits[i]<=0) continue;	// for some reason cmodels sometimes stores id -1

//		string n=retrieve_name(INPUT,answerset_lits[i]);
		const char *n=retrieve_name(INPUT,answerset_lits[i]);

		if (!forced_pure_asp && *pure_asp /* spare the comparison if not needed */ && 
		    /* "required" allows to capture programs with defined parts but no CSP variables */
		    (startsWith(n,"cspvar(") || startsWith(n,"required(")))
			*pure_asp=false;

		if (n[0]!=0)
			fp << n << " ";
//else
//fp << endl << "PROBLEM with ID " << answerset_lits[i] << endl;
	}
clog << "after pure-check: " << get_total_cpu() << endl;
	fp << endl;

	fp.close();

	if (!forced_pure_asp)	/* if we *already* know that it is pure asp, we take shortcuts */
	{	TFILE1=INPUT;	// now we use the input as temporary output file [DANGER!!!!!]
		timed_cppsystem("mkatoms -a < \""+ASP_MOD+"\" > \""+TFILE1+"\"");
	}

	return(true);
}

#endif /* HAVE_CMODELS */

/*
 * Returns true if a model was found (and stored in ASP_MOD) and false otherwise.
 */
bool call_basic_solver(cmdline_params p,string INPUT,string ASP_MOD,bool *pure_asp,bool forced_pure_asp)
{	string TFILE1;

	timed_cppsystem(p.SOLVER+" < \""+INPUT+"\" > \""+ASP_MOD+"\"");

	if (forced_pure_asp)	/* we *already* know that it is pure asp: take shortcuts! */
	{	*pure_asp=true;
		if (my_grep_startsWith_firstLine("False",ASP_MOD,false,false))
			return(false);
		return(true);
	}

	TFILE1=INPUT;	// now we use the input as temporary output file [DANGER!!!!!]
	/* check if the program was consistent */
	timed_cppsystem("mkatoms -a < \""+ASP_MOD+"\" > \""+TFILE1+"\"");
//	if (my_egrep("%\\*\\*\\* no models found",TFILE1,false,false))
	if (my_grep_startsWith_firstLine("%*** no models found",TFILE1,false,false))
		return(false);

	/* check if this is a pure ASP program */
	/* "required" allows to capture programs with defined parts but no CSP variables */
	*pure_asp=!my_grep_startsWith("cspvar(",TFILE1,1,false,false) && !my_grep_startsWith("required(",TFILE1,1,false,false);

	return(true);
}

/*
 * Returns true if a model was found (and stored in ASP_MOD) and false otherwise.
 */
bool call_asp_solver(cmdline_params p,string INPUT,string ASP_MOD,bool *pure_asp,bool forced_pure_asp,int MODELS)
{
extern bool DEVELOPMENT_VER;
if (DEVELOPMENT_VER)
{
cerr << "FIXME: call_asp_solver() calls two functions that silently modify param file INPUT and ezcsp *heavily* relies on this modification!!!" << std::endl;
}
#ifdef HAVE_CMODELS
	if (p.use_cmodels_incremental)
		return(call_cmodels(p,INPUT,ASP_MOD,pure_asp,forced_pure_asp,MODELS+1));
#endif /* HAVE_CMODELS */
	return(call_basic_solver(p,INPUT,ASP_MOD,pure_asp,forced_pure_asp));
}

bool is_relevant_atom(const char *n)
{	const char *relevant[]=
	{	"cspdomain(", "domain(",
		"cspvar(", "var(",
		"required(",
		"label_order(",
		"label_option(",
		"lpinteger(",
		"lpobjective(",
		NULL
	};

	for(int i=0;relevant[i]!=NULL;i++)
		if (startsWith(n,relevant[i]))
			return(true);

	/* Atoms of the form <PL_RElATION_PREFIX>XXX are input for the defined part */
	if (startsWith(n,PL_RELATION_PREFIX))
		return(true);

	return(false);
}

#ifdef HAVE_CMODELS
void append_denial_cmodels(string PARSED,bool full_model)
{	
	if (all_models_found) return;	// All models have already been found -- no need to add the denials (and cmodels right now crashes if we try to)

	int *constraint_lits=new int [names.size()+1];
	int j;

	bool found[names.size()+1];
	for(int i=0;i<=(int)names.size();found[i++]=false);
	j=0;
	for(int i=0;i<num_atoms;i++)
	{	//if (answerset_lits[i]<=0) continue;	// for some reason cmodels sometimes stores id -1

		found[answerset_lits[i]]=true;	// mark found in the answer set
		if (full_model || is_relevant_atom(retrieve_name(PARSED,answerset_lits[i])))	// only add to the denial the relevant atoms (i.e. cspdomain, cspvar, etc.)
			constraint_lits[j++]=(answerset_lits[i]<<1)+0;	// +0 because the extended literal is positive (i.e. not under default negation)
	}
	
	for(int i=1;i<=(int)names.size();i++)
	{	if (found[i]) continue;

		/* WARNING: not outputting the unnamed literals will not play well in combination with #hide,
		 *          but we have no choice. Allowing certain unnamed literals in the constraint
		 *          causes the appearance of redundant models.
		 */
		if ((full_model && retrieve_name(PARSED,i)[0]!=0) ||
		    (!full_model && is_relevant_atom(retrieve_name(PARSED,i))))
			constraint_lits[j++]=(i<<1)+1;	// +1 because the extended literal is under default negation
	}

	/* addDenial() assumes that the literals are sorted by id */
	qsort(constraint_lits,j,sizeof(int),cmpintp);

	if (ctable.addDenial(constraint_lits,j)==false)
		program_is_already_inconsistent=true;

	delete constraint_lits;
}
#endif /* HAVE_CMODELS */

void append_denial(cmdline_params p,string ASP_MOD,string PARSED,string TFILE1,string DEST,bool full_model)
{	fstream fp,fpo;

	ensure_names_loaded(PARSED);	/* ensure vectors names and names_hash are filled */

#ifdef HAVE_CMODELS
	if (p.use_cmodels_incremental)
	{	append_denial_cmodels(PARSED,full_model);
		if (!p.save_search_state)
			// If we are not required to save the search state
			// upon termination of ezcsp, then there is no
			// need to write the denial to DEST.
			return;
	}
#endif /* HAVE_CMODELS */

	// Hand-create the denials to reject the previous ASP model.
	// We have to hand-create it because lparse tends to stall
	// when parsing this type of denials.


	fpo.open(DEST.c_str(),ios::out | ios::app);
	if (fpo.fail())
	{	open_err(DEST);
		//rm_all_files(ALL_FILES);
		//exit(1);
	}

	// output the size of the body
	timed_cppsystem("mkatoms -n < \""+ASP_MOD+"\" > \""+TFILE1+"\"");

	fp.open(TFILE1.c_str(),ios::in);
	if (fp.fail())
	{	open_err(TFILE1);
		//rm_all_files(ALL_FILES);
		//exit(1);
	}

	bool found[names.size()+1];
	for(int i=0;i<=(int)names.size();found[i++]=false);
	vector<int> bodyPos,bodyNeg;
	while(!fp.eof())
	{	string atom;
		int id;

		getline(fp,atom);
		if (fp.fail()) break;

		atom=trim(atom);

		if (!full_model && !is_relevant_atom(atom.c_str()))	// only add to the denial the relevant atoms (i.e. cspdomain, cspvar, etc.)
			continue;

		// We need to look for $atom at the END of the line
		// in $PARSED.
		// Notice that we need to ensure that nothing follows
		// $atom in the line (e.g. atom "a" could match "a2"
		// otherwise).
		// Because egrep doesn't work properly because we
		// may have parenteses in the atoms, we append a |
		// at the end of each line of $PARSED and then
		// grep for "$atom|".
		//$id=trim(`cat "$PARSED" | sed -e 's/\\(.*\\)/\\1|/' | grep ' $atom|' | sed -e 's/^\\([0-9]*\\)[^0-9].*/\\1/'`);
		id=retrieve_id(PARSED,atom);

		found[id]=true;	// mark found in the answer set

		//fpo << id << " ";
		bodyPos.push_back(id);
	}
	fp.close();

	for(int i=1;i<=(int)names.size();i++)
	{	if (found[i]) continue;

		/* WARNING: not outputting the unnamed literals will not play well in combination with #hide,
		 *          but we have no choice. Allowing certain unnamed literals in the constraint
		 *          causes the appearance of redundant models.
		 */
		if ((full_model && retrieve_name(PARSED,i)[0]!=0) ||
		    (!full_model && is_relevant_atom(retrieve_name(PARSED,i))))
			bodyNeg.push_back(i);
	}

	fpo << "1 1 " << (bodyPos.size()+bodyNeg.size()) << " " << bodyNeg.size();

	for(int i=0;i<(int)bodyNeg.size();i++)
		fpo << " " << bodyNeg[i];

	for(int i=0;i<(int)bodyPos.size();i++)
		fpo << " " << bodyPos[i];
	fpo << endl;

	fpo.close();
}
