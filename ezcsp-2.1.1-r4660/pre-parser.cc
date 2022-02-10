/*
 * pre-parser
 *
 * by Marcello Balduccini (marcello.balduccini@gmail.com)
 *
 * Copyright (C) 2009-2021 Marcello Balduccini. All Rights Reserved.
 *
 * Pre-processor allowing to specify EZCSP constraints with the
 * traditional infix notation, e.g.
 *    required(st(X) + 2 > e(X)).
 *
 * An attempt is made to support both lparse syntax and dlv syntax.
 *
 * The parser also processes #sig signature specifications from dlv_rsig.
 *
 * Run with:
 *
 *   pre-parser file1 [file2 ...]
 *
 * The program will output the target program to the console. To store the
 * target program in a file, use redirection. For example, to parse files
 * "main-file.lp" and "extra-file.lp" and store the result in file
 * "parsed.lp", use:
 *
 *   pre-parse main-file.lp extra-file.lp > parsed.lp
 *
 *
 * Example files
 * ==================
 *
 *-------------------------------------

%Example
%
required(st(X) + d(X) >= e(Y)) :- l1(X), l2(Y).

 *-------------------------------------

%Example
%
required(sum([p(X)/2],<,5)).

 *-------------------------------------
 *   
 *
 *   History
 *  ~~~~~~~~~
 *   
 *   09/09/10 - [1.8] Added support for sin, cos, tan, pow, exp.
 *   11/03/09 - [1.7] Added support for reified negation (#!, translated
 *                    as #\ for Sicstus).
 *   07/31/09 - [1.6] Added aliases for reified csp constraint operators
 *                    (e.g. \/ for #\/, /\ for #/\).
 *   07/31/09 - [1.5] Added detection of CR-Prolog programs.
 *   07/29/09 - [1.4] Added support for reified csp constraint operators
 *                    (#\/, #/\, etc.).
 *   11/03/08 - [1.3] Common code separated out as a library.
 *   11/03/08 - [1.2] Parser entirely rewritten from principled foundations.
 *                    Rewritten code is shared with EZCSP's pre-parser.
 *                    Parsing functions now imported from dlv_rsig's parser
 *                    library.
 *   10/24/08 - [1.1] Added the ability to deal with infix notation.
 *
 */

#include "config.h"

#include <iostream>
#include <fstream>

#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <string.h>

#include <string>
#include <vector>

#include <aspparser/parser.h>

#include "common.h"

#define VERSION "1.8"

/* debug flags */
//#define DEBUG_TREE 1

//using namespace std;

bool is_number(struct item *a)
{	if (a->arity!=0) return(false);

	return(is_floating_point(a->relation) || is_integer(a->relation));
}

bool is_floating_pointx(struct item *a)
{	if (a->arity!=0) return(false);

	return(is_floating_point(a->relation));
}

void translate_floating_point(struct item *a)
{	char *fp;

	fp=a->relation;
	a->relation=(char *)calloc(strlen(fp)+3,sizeof(char));
	sprintf(a->relation,"\"%s\"",fp);
	free(fp);
}

void process_constraints(struct item *a)
{	int i;

	struct 
	{	char *from, *to;
	} map[]=
	{	{ (char *)">", (char *)"ezcsp__gt" },
		{ (char *)"#>", (char *)"ezcsp__gt" },

		{ (char *)">=", (char *)"ezcsp__geq" },
		{ (char *)"#>=", (char *)"ezcsp__geq" },

		{ (char *)"<", (char *)"ezcsp__lt" },
		{ (char *)"#<", (char *)"ezcsp__lt" },

		{ (char *)"=<", (char *)"ezcsp__leq" },
		{ (char *)"#=<", (char *)"ezcsp__leq" },
		{ (char *)"<=", (char *)"ezcsp__leq" },
		{ (char *)"#<=", (char *)"ezcsp__leq" },

		{ (char *)"=", (char *)"ezcsp__eq" },
		{ (char *)"#=", (char *)"ezcsp__eq" },
		{ (char *)"==", (char *)"ezcsp__eq" },
		{ (char *)"#==", (char *)"ezcsp__eq" },

		{ (char *)"!=", (char *)"ezcsp__neq" },
		{ (char *)"#!=", (char *)"ezcsp__neq" },
		{ (char *)"\\=", (char *)"ezcsp__neq" },
		{ (char *)"#\\=", (char *)"ezcsp__neq" },

		/* Prolog */
		{ (char *)"#:-", (char *)"ezcsp__prolog_if" },
		{ (char *)"#,", (char *)"ezcsp__prolog_body" },
		{ (char *)"#?-", (char *)"ezcsp__prolog_query" },
		{ (char *)"?-", (char *)"ezcsp__prolog_query" },
		/* */

		{ (char *)"#->", (char *)"ezcsp__impl_r" },
		{ (char *)"->", (char *)"ezcsp__impl_r" },
		{ (char *)"#<-", (char *)"ezcsp__impl_l" },
		{ (char *)"<-", (char *)"ezcsp__impl_l" },

		{ (char *)"#\\/", (char *)"ezcsp__or" },
		{ (char *)"\\/", (char *)"ezcsp__or" },
		{ (char *)"#/\\", (char *)"ezcsp__and" },
		{ (char *)"/\\", (char *)"ezcsp__and" },
		{ (char *)"#\\", (char *)"ezcsp__xor" },
		{ (char *)"\\", (char *)"ezcsp__xor" },
		{ (char *)"#<=>", (char *)"ezcsp__diff" },
		{ (char *)"<=>", (char *)"ezcsp__diff" },
		{ (char *)"#!", (char *)"ezcsp__not" },

		{ (char *)"+", (char *)"ezcsp__pl" },
		{ (char *)"-", (char *)"ezcsp__mn" },
		{ (char *)"*", (char *)"ezcsp__tm" },
		{ (char *)"/", (char *)"ezcsp__dv" },
		{ (char *)"**", (char *)"ezcsp__starstar" },
		{ (char *)"div", (char *)"ezcsp__div" },
		{ (char *)"mod", (char *)"ezcsp__mod" },
		{ (char *)"max", (char *)"ezcsp__max" },
		{ (char *)"min", (char *)"ezcsp__min" },
		{ (char *)"abs", (char *)"ezcsp__abs" },
		{ (char *)"pow", (char *)"ezcsp__pow" },	// NEW FROM HERE
		{ (char *)"exp", (char *)"ezcsp__exp" },
		{ (char *)"sin", (char *)"ezcsp__sin" },
		{ (char *)"cos", (char *)"ezcsp__cos" },
		{ (char *)"tan", (char *)"ezcsp__tan" },

		{ (char *)"sum", (char *)"ezcsp__sum" },

		{ NULL, NULL}
	};

	/* negative numbers */
	if (strcmp(a->relation,"-")==0 && a->arity==1 && is_number(a->args[0]))
	{	free(a->relation);
		a->relation=(char *)calloc(strlen(a->args[0]->relation)+2,sizeof(char));
		sprintf(a->relation,"-%s",a->args[0]->relation);
		free(a->args[0]->relation);
		free(a->args);
		a->arity=0;
	}

	for(i=0;map[i].from!=NULL;i++)
	{	if (strcmp(a->relation,map[i].from)==0)
		{	
//fprintf(stderr,"match! %s/%d\n",a->relation,a->arity);
		
			free(a->relation);

			a->relation=strdup(map[i].to);
			a->is_infix=0;

			break;
		}
	}

	/* process intensionally represented lists, e.g. [ st(X) / 2 ] */
	if ((strcmp(a->relation,"[")==0) && (a->arity==1) &&
	    (strcmp(a->args[0]->relation,"/")==0) && (a->args[0]->arity==2))
	{	struct item *i;

//printf("match! [ Lit / Arity ]\n");

		i=a->args[0];

		free(a->relation);
		a->relation=strdup("list");

		free(a->args);

		a->arity=2;
		a->args=i->args;

		free(i);

		a->is_parenthesis=0;
	}
	else
	if ((strcmp(a->relation,"[")==0) && (a->arity>=1))
	{	free(a->relation);
		a->relation=strdup("extlist");
		a->is_parenthesis=0;
	}
	else

	/* process floating-point numbers */
	if (is_floating_pointx(a))
		translate_floating_point(a);


/*
	if (strcmp(a->relation,"[")==0)
		{	fprintf(stderr,"got relation [; args=%d\n",a->arity);
			for(int i=0;i<a->arity;i++)
				fprintf(stderr,"arg %d: %s\n",i,a->args[i]->relation);
		}
	}
*/

	for(i=0;i<a->arity;i++)
		process_constraints(a->args[i]);

/*
	for(i=0;i<n_rsigs;i++)
	{	if (strcmp(atom->relation,rsigs[i]->relation)==0 &&
		    atom->arity==rsigs[i]->arity)
		{	for(j=0;j<atom->arity;j++)
			{	if (buff[0]!=0) strcat(buff,", ");

				sprintf(&buff[strlen(buff)],"%s(%s)",rsigs[i]->args[j]->relation,atom->args[j]->string);

				if (atom->args[j]->arity>0) add_domains(buff,atom->args[j]);
			}
		
			return;
		}
	}
*/
}

void process_floating_point(struct item *a)
{	int i;

	/* process floating-point numbers */
	if (is_floating_pointx(a))
		translate_floating_point(a);
	else
		for(i=0;i<a->arity;i++)
			process_floating_point(a->args[i]);
}

void process_constraints_in_rule(struct rule *r,bool *is_crprolog)
{	int i;

	if (r->type==RULE_SYSTEM_DIRECTIVE) return;	// nothing to be done

	if (r->type==RULE_CR_RULE) *is_crprolog=true;	// detect cr-rules

	for(i=0;i<r->head_size;i++)
	{	if (strcmp(r->head[i]->relation,"required")==0 && (r->head[i]->arity==1))
			process_constraints(r->head[i]->args[0]);
		else
		/* the only thing we need to do for label_option is renaming min/max to ezcsp__min/max */
		if (strcmp(r->head[i]->relation,"label_option")==0 && (r->head[i]->arity==1))
			process_constraints(r->head[i]->args[0]);
		else
		if (strcmp(r->head[i]->relation,"lpobjective")==0 && (r->head[i]->arity==1))
			process_constraints(r->head[i]->args[0]);
		else
			process_floating_point(r->head[i]);
	}

	for(i=0;i<r->body_size;i++)
	{	if (strcmp(r->body[i]->relation,"required")==0 && (r->body[i]->arity==1))
			process_constraints(r->body[i]->args[0]);
		else
			process_floating_point(r->body[i]);
	}
}

/*
 * [100315] No longer needed. Functionality now embedded in dlv_rsig [1.8.8+].

// Now that the program has been loaded, remove prefix "#verbatim "
// from the lines that were declared "unparsable".
void clear_verbatim(struct node *program)
{	struct node *prev,*n;

#define VERBATIM_STRING "#verbatim "

	prev=program;
	for(n=program->next;n!=NULL;prev=n,n=n->next)
	{	struct rule *r;

		r=n->data;
		if (r->type==RULE_SYSTEM_DIRECTIVE && startsWith(r->system_directive,VERBATIM_STRING))
		{	char *d=strdup(&r->system_directive[strlen(VERBATIM_STRING)]);
			free(r->system_directive);
			r->system_directive=d;
		}
	}
}
*/

struct node *ezcsp_extract_defined_part(struct node *program)
{	struct node *prev,*n,*d;
	struct node *defined;
	bool in_defined;

	defined=(struct node *)calloc(1,sizeof(struct node));
	d=defined;

	in_defined=false;
	prev=program;
	for(n=program->next;n!=NULL;prev=n,n=n->next)
	{	struct rule *r;

		r=n->data;
		if (r->type==RULE_SYSTEM_DIRECTIVE && startsWith(r->system_directive,"#begin_defined."))
		{	in_defined=true;
			prev->next=n->next;
			n=prev;
		}
		else
		if (r->type==RULE_SYSTEM_DIRECTIVE && startsWith(r->system_directive,"#end_defined."))
		{	in_defined=false;
			prev->next=n->next;
			n=prev;
		}
		else
		if (in_defined)
		{	d->next=n;
			d=n;
			
			prev->next=n->next;
			
			n->next=NULL;
			
			n=prev;
		}
	}

	return(defined);
}

void ezcsp_preparse(std::vector<std::string> flist,std::vector<bool> fpure_list,std::string ofile,std::string efile,std::string defpart_file,bool *is_crprolog)
{	int n_files;
	char **files;
	struct node *program,*n;

	FILE *fpo,*fpe,*fpd;

	if (ofile=="-")
		fpo=stdout;
	else
	{	fpo=fopen(ofile.c_str(),"w");
		if (fpo==NULL)
		{	// fix here!!!
			fprintf(stderr,"ERROR\n");
			exit(1);
		}
	}

	if (defpart_file=="-")
		fpd=stdout;
	else
	{	fpd=fopen(defpart_file.c_str(),"w");
		if (fpd==NULL)
		{	// fix here!!!
			fprintf(stderr,"ERROR\n");
			exit(1);
		}
	}

	/*
	 * FIXME: efile is unused
	 */
	if (efile=="-")
		fpe=stderr;
	else
	{	fpe=fopen(efile.c_str(),"w");
		if (fpe==NULL)
		{	// fix here!!!
			fprintf(stderr,"ERROR\n");
			exit(1);
		}
	}

	if (flist.size()==0)
	{	n_files=1;
		files=NULL;
	}
	else
	{	files=(char**)calloc(flist.size(),sizeof(char *));
		n_files=0;
		for(int i=0;i<(int)flist.size();i++)
		{	if (fpure_list[i])
				files[n_files++]=strdup(flist[i].c_str());
		}
		//n_files=flist.size();
	}

	program=parse_program(n_files,files);


#ifdef DEBUG_TREE
	debug_show_program(program);
#endif

// [100315] No longer needed. Functionality now embedded in dlv_rsig [1.8.8+].
//	clear_verbatim(program);

	struct node *defined_part=ezcsp_extract_defined_part(program);

	add_domains_to_program(program);

	*is_crprolog=false;
	for(n=program->next;n!=NULL;n=n->next)
		process_constraints_in_rule(n->data,is_crprolog);

	output_program_to_file(program,fpo);

	output_program_to_file(defined_part,fpd);

	/* force the showing of the relations that define the csp */
/*
 * [marcy 111016] Disabled because of incompatibilities between gringo 3.x and 4.x.
	fprintf(fpo,"#show cspvar/3.\n");
	fprintf(fpo,"#show required/1.\n");
	fprintf(fpo,"#show cspdomain/1.\n");
	fprintf(fpo,"#show label_order/2.\n");
	fprintf(fpo,"#show label_option/1.\n");
*/
/*
 * OLD-style #show statements
	fprintf(fpo,"#show cspvar(X,Y,Z).\n");
	fprintf(fpo,"#show required(X).\n");
	fprintf(fpo,"#show cspdomain(X).\n");
	fprintf(fpo,"#show label_order(X,Y).\n");
	fprintf(fpo,"#show label_option(X).\n");
*/

	if (fpo!=stdout) fclose(fpo);
	if (fpe!=stderr) fclose(fpe);
	if (fpd!=stdout) fclose(fpd);

	std::fstream fx;
	std::ostream *pfx;

	if (ofile=="-")
		pfx=&std::cout;
	else
	{	fx.open(ofile.c_str(),std::ios::out | std::ios::app);
		if (fx.fail())
		{	// fix here!!!
			fprintf(stderr,"ERROR\n");
			exit(1);
		}
		pfx=&fx;
	}

	for(int i=0;i<(int)flist.size();i++)
	{	if (!fpure_list[i])
			myreadfile(flist[i],pfx);
	}
}

void ezcsp_preparse(std::vector<std::string> flist,std::vector<bool> fpure_list,std::string ofile,std::string efile,std::string defpart_file)
{	bool is_crprolog;

	ezcsp_preparse(flist,fpure_list,ofile,efile,defpart_file,&is_crprolog);
}

#ifdef COMPILE_PRE_PARSER_MAIN
int main(int argc,char *argv[])
{	std::vector<std::string> files;
	std::vector<bool> fpure_list;

	fprintf(stderr,"pre-parser version "VERSION"...\n");
	fprintf(stderr,"parser version %s...\n\n",parser_version());

	if (argc<=1 || strcmp(argv[1],"-h")==0 || (argc>2 && strcmp(argv[1],"--")==0))
	{	fprintf(stderr,"Usage:\n");
		fprintf(stderr,"       pre-parser --     processes input from console (CTRL+D to terminate input on Unix)\n");
		fprintf(stderr,"       pre-parser <file1> [<file2> [...]]    processes input files file1,file2,...\n");
		fprintf(stderr,"       pre-parser -h     prints this help\n\n");

		exit(1);
	}

	if (strcmp(argv[1],"--")!=0)
	{	for(int i=1;i<argc;i++)
		{	files.push_back(argv[i]);
			fpure_list.push_back(true);
		}
	}

	ezcsp_preparse(files,fpure_list,"-","-","-");

	exit(0);
}
#endif
