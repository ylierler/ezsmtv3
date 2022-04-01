#include "config.h"

#include <fstream>
#include <iostream>

#include <string>
#include <vector>

/* for exit(), atoi() */
#include <stdlib.h>

/* for strlen() */
#include <string.h>

#ifdef HAVE_UNISTD_H
/* for unlink() */
#  include <unistd.h>
#endif

#include "common.h"

#include "phpemu.h"

#include "cp_solver.h"

#include "output_model.h"

//using namespace std;
using namespace phpemu;

#define clen 10240

#define MOD_NONE	0
#define MOD_SMODELS	1
#define MOD_DLV		2
#define MOD_CMODELS	3
#define MOD_CLASP	4

int trimNewLines(char *line)
{	int l;
	int new_line;

	new_line=0;
	for(l=strlen(line);
	    l>0 && (line[l-1]=='\n' || line[l-1]=='\r');
	    l--)
	{	line[l-1]=0;
		new_line=1;
	}
	return(new_line);
}

/* check if the line is "Answer: ###" */
int is_answer_line(char *l)
{	return(startsWith(l,"Answer:"));
}

int is_smodels_model(char *l)
{	return(startsWith(l,"Stable Model:"));
}

int is_dlv_model(char *l)
{	if (startsWith(l,"Best model:"))
		return(1);

	return(l[0]=='{');
}

int is_cmodels_model(char *l)
{	return(startsWith(l," Answer set:"));
}

int is_model(char *l,int prev_line_was_answer_num,int *type)
{	int new_type=MOD_NONE;

	if (is_smodels_model(l))
		new_type=MOD_SMODELS;
	else if (is_dlv_model(l))
		new_type=MOD_DLV;
	else if (is_cmodels_model(l))
		new_type=MOD_CMODELS;
	else if (prev_line_was_answer_num)
		/* Clasp format:
		 * line 1: Answer: ### 
		 * line 2 has no prefix -- it starts with the model right away.
		 */
		new_type=MOD_CLASP;
	else
		return(0);

	if (*type==MOD_NONE)
	{	*type=new_type;
		return(1);
	}

	return(new_type==*type);
}

#if !defined(HAVE_MKSTEMP) && defined(HAVE_MKSTEMPS)
extern int mkstemps (char *pattern, int suffix_len); 
#endif

bool mkatoms(FILE *fpi,bool one_per_line,bool show_endmodel_marker=true,bool A_prolog_like=false,int MODEL_NUM=1)
{	char *line,*p=NULL,*tline;
	int table=0;
	int meta_model=0;
	long pos;
	int /*tnl,*/new_line;
	FILE *fp;
	int t,crlf_addon=0;
	int prev_line_was_answer_num;
	int models;
	int type;
	int inside_quotes;

	line=(char *)calloc(clen+1,sizeof(char));

	if (table)
	{	
		char *tmpdir;
#ifdef __MINGW32__
		tmpdir=getenv("TEMP");
		if (tmpdir==NULL)
#endif
		tmpdir="/tmp";
		sprintf(line,"%s/tmp.XXXXXX",tmpdir);

#ifdef HAVE_MKSTEMP
		t=mkstemp(line);
#else
#  ifdef HAVE_MKSTEMPS
 	        t=mkstemps(line,0);
#  else
#    error "Either mkstemp() or mkstemps() must be available."
#  endif
#endif
		if (t<0)
		{	fprintf(stderr,"Unable to create temp file. With Windows, make sure directory C:\\tmp exists.\n");
			exit(1);
		}
		fp=fdopen(t,"wt");
		if (fp==NULL)
		{	fprintf(stderr,"Unable to create temp file. With Windows, make sure directory C:\\tmp exists.\n");
			exit(1);
		}
		fprintf(fp,"\n");
		crlf_addon=ftell(fp)-1;
		fclose(fp);
		unlink(line);
	}

	line[0]=0;

	pos=0;
	new_line=1;
	prev_line_was_answer_num=0;
	models=0;
	type=MOD_NONE;
	while (!feof(fpi/*stdin*/))
	{	if (fgets(line,clen,fpi/*stdin*/)==NULL)
			break;

/*
 * ASSUMPTION
 *
 * Every line that does not contain a model is shorter than clen.
 */

		//tnl=new_line;
		new_line=0;
		new_line=trimNewLines(line);

		if (/*(tnl) && */(is_answer_line(line)))
		{	prev_line_was_answer_num=1;
			continue;
		}

		if (/*(tnl) && */(is_model(line,prev_line_was_answer_num,&type)))
		{	int read_more,trm,i=0;
			char *l;

			if (!one_per_line)
			{	std::cout << "Answer: " << (MODEL_NUM++) << std::endl;
				std::cout << "Stable Model: ";
			}

			models++;
			if (table)
				fprintf(stderr,"%ld\n",pos);

			tline=line;

			switch(type)
			{	case MOD_SMODELS:
				case MOD_CMODELS:
					while (*tline!=':') tline++;
					tline+=2; 	/* skip leading space */
					break;
				case MOD_DLV:
					while (*tline!='{') tline++;
					tline++;	/* skip leading '{' */
					break;
				case MOD_CLASP:
					/* nothing to be skipped on model line */
					break;
			}

			read_more=!new_line;
			do
			{	l=tline;

				inside_quotes=0;

				/* check if there are more atoms to read -- see comment below about '}' */
				while ((*l) && (*l!='}'))
				{	p=l;

					/* Find the end of the current atom. This is accomplished
					 * by looking for a delimiter.
					 * ' ' is ok for both smodels and dlv, since the delimiter
					 * for dlv is ', ', and the delimiter for smodels is ' '.
					 * 
					 * Also, we can check for '}' independently of the engine,
					 * since '}' never occurs in the output of smodels.
					 *
					 * Additionally, we have to keep track of escaped quotes (\"),
					 * as those do not count as string delimiters.
					 */
//					while ((*l!=' ') && (*l) && (*l!='}')) l++;
					int escaped=0;
					while ((*l) && (inside_quotes || ((*l!='}') && (*l!=' '))))
					{	if (!escaped && *l=='\"') inside_quotes=!inside_quotes;
						escaped=(*l=='\\');
						l++;
					}

					/* if parsing dlv, remove the comma before the space*/
					if ((type==MOD_DLV) && (*l==' ') && (*(l-1)==','))
						*(l-1)='x';

					if (((*l)==0) && (read_more))		/* if the line did not fit in the buffer... */
					{	for(i=0;i<(int)(l-p);i++)	/* ...move the rest of the line to the beginning */
							line[i]=p[i];		/* of the buffer... */
						line[i]=0;
						l=&line[i];			/* ...and make sure we exit the while loop */
					}
					else
					{	
						*l=0;				/* otherwise, output the current atom */
						if ((type==MOD_DLV) && (*(l-1)=='x'))	/* if parsing dlv, make sure the space that replaced the comma is removed. */
							*(l-1)=0;
						l++;
//						pos+=printf("%s%s",p,(A_prolog_like) ? ".\n":"\n")+crlf_addon;
						if (meta_model) pos+=printf("holds_in(");
						pos+=printf("%s",p);
						if (meta_model) pos+=printf(",%d)",models);
						/* terminate the line */
						if (A_prolog_like) pos+=printf(".");
						if (one_per_line)
							pos+=printf("\n")+crlf_addon;
						else
							pos+=printf(" ");
						i=0;
					}
				}
				trm=read_more;
				if (read_more)	/* if the line did not fit in the buffer, we have to read again */
				{	tline=line;
					if (fgets(&line[i],clen-i,fpi/*stdin*/)==NULL)
					{	if (i>0)	/* if the file is over and we still have an atom to write, write it */
							pos+=printf("%s%s",p,(A_prolog_like) ? ".\n":"\n")+crlf_addon;
						break;
					}

					read_more=!trimNewLines(line);
					//read_more=1;
					//while ((line[strlen(line)-1]=='\n') ||
					//       (line[strlen(line)-1]=='\r'))
					//{	line[strlen(line)-1]=0;
					//	read_more=0;
					//}
				}
			} while(trm);

//			if (show_endmodel_marker && one_per_line && (!meta_model || A_prolog_like))
//				pos+=printf("%sendmodel\n",(A_prolog_like) ? "%%":"::")+crlf_addon;

		}

		prev_line_was_answer_num=0;
	}

//	if (one_per_line && models==0)
//		printf("%s no models found.\n",(A_prolog_like) ? "%***":"***");

//	else
//	if (!one_per_line)
//		printf("\n%s\n",(models==0) ? "False":"True");

	return(models!=0);
}

/*
 * Returns false if no model; true otherwise.
 */
bool output_raw_aset(cmdline_params p,std::string ASP_MOD,int MODELS)
{	FILE *fp;
	bool res;

	fp=fopen(ASP_MOD.c_str(),"r");
	if (fp==NULL)
		open_err(ASP_MOD);

	res=mkatoms(fp,p.MKATOMS/*one-per-line*/,true/*-n*/,(p.MKATOMS && p.AFLAG!=""),(MODELS+1));
	
	fclose(fp);
	
	return(res);
}

void output_aset(cmdline_params p,std::string ASP_MOD,std::string TFILE1,int MODELS)
{	std::fstream fp;

	if (p.MKATOMS)
		timed_cppsystem("mkatoms -n "+p.AFLAG+" < \""+ASP_MOD+"\"");
	else
	{	timed_cppsystem("mkatoms -n < \""+ASP_MOD+"\" > \""+TFILE1+"\"");

		std::cout << "Answer: " << (MODELS+1) << std::endl;
		std::cout << "Stable Model: ";
		fp.open(TFILE1.c_str(),std::ios::in);
		if (fp.fail())
		{	open_err(TFILE1);
			//rm_all_files(ALL_FILES);
			//exit(1);
		}

		while(!fp.eof())
		{	std::string line;

			getline(fp,line);
			if (fp.fail()) break;

			line=trim(line);

			std::cout << line << " ";
		}
		fp.close();
	}
}

void output_csp_solution(cmdline_params p,std::string CSP_MOD)
{	std::fstream fp;

	// here and later, we use "(.*\)[^0-9.].*" for the end of the line because
	// when we run through the linux emulation some \r chars are added to the end
	// of the line, and we need to get rid of them.
	//
	//Note that we also convert back single quotes to double quotes.
	//

	fp.open(CSP_MOD.c_str(),std::ios::in);
	if (fp.fail())
	{	open_err(CSP_MOD);
		//rm_all_files(ALL_FILES);
		//exit(1);
	}

	while(!fp.eof())
	{	std::string line;
		bool recognized;

		std::vector<std::string> matches;

		getline(fp,line);
		if (fp.fail()) break;

		line=trim(line);

		recognized=true;
//		if (preg_match("\\+\\+(.*[a-zA-Z0-9')])=(.*)",line,matches))
		if (is_cp_equality_statement(line,matches))
		{	if (matches[2]=="ezcspvarundef")
				recognized=false;
			else
			{	if (p.AFLAG=="")
					line=matches[1]+"="+matches[2];
				else
				{	std::string quotes="";
					if (is_floating_point(matches[2]))
						quotes="\"";
					line=((std::string)"cspeq(")+matches[1]+","+quotes+matches[2]+quotes+")";
				}
			}
		}
		else
/*		if (is_cp_inequality_statement(line,matches))
		{	if (p.AFLAG=="")
				line=matches[1]+matches[2]+matches[3];
			else
				line=((std::string)"cspineq(")+matches[1]+matches[2]+matches[3]+")";
		}
		else
*/		if (is_cp_statement(line,matches))
		{	if (p.AFLAG=="")
				line=matches[1];
			else
				line=((std::string)"cspmisc(")+matches[1]+")";
		}
		else
			recognized=false;

		if (recognized)
		{	std::cout << str_replace("'","\"",line);

			if (p.MKATOMS)
			{	if (p.AFLAG!="")
					std::cout << ".";
				std::cout << std::endl;
			}
			else
				std::cout << " ";
		}
		
	}
	fp.close();
}

void output_extended_aset_footer(cmdline_params p)
{	if (p.MKATOMS)
	{	if (p.AFLAG=="")
			std::cout << "::endmodel" << std::endl;
		else
			std::cout << "%%endmodel" << std::endl;
	}
	else
		std::cout << std::endl;
}

/*
 * Returns false if no model; true otherwise.
 */
bool output_pure_aset(cmdline_params p,std::string ASP_MOD,std::string TFILE1,int MODELS)
{	std::fstream fp;
	bool consistent;

	consistent=output_raw_aset(p,ASP_MOD,MODELS);
	//output_aset(p,ASP_MOD,TFILE1,MODELS);

	if (consistent)
		output_extended_aset_footer(p);

	return(consistent);
}

void output_extended_aset(cmdline_params p,std::string ASP_MOD,std::string CSP_MOD,std::string TFILE1,int MODELS)
{	std::fstream fp;

	output_aset(p,ASP_MOD,TFILE1,MODELS);

	output_csp_solution(p,CSP_MOD);

	output_extended_aset_footer(p);
}
