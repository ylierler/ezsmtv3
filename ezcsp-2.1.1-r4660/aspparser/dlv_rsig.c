/*
 * dlv_rsig
 *
 * by Marcello Balduccini (marcello.balduccini@gmail.com)
 *
 * Copyright (C) 2009-2015 Marcello Balduccini. All Rights Reserved.
 *
 * Pre-processor allowing to specify sorts for the arguments
 * of relations and functions in dlv programs.
 *
 * Supported syntax:
 *   1) Disjunctive rules are allowed (a(X) v b(X) v ...).
 *   2) Anonymouse variables (i.e. "_") are allowed.
 *   3) Default and strong negations are allowed (even in combination).
 *   4) Built-in dlv relations, such as #succ, are allowed.
 *   5) Lists are allowed.
 *   6) Aggregates are allowed.
 *   7) dlv-style declarations, such as #include <ListAndSet>, are allowed.
 *
 * Signature declarations are specified by a #sig declaration, e.g.
 *
 *     #sig a(p,q), b(q).
 *
 * says that the domain of the first argument of a is p; the domain of the
 * second argument is q; and the domain of the argument of b is q.
 * Signatures can be specified for both predicates and functions.
 * ASSUMPTION: function names and predicate names are DISJOINT.
 *
 * Domains are defined as usual, by defining the corresponding relations, e.g.
 *
 *    p(x). p(y). p(z).
 *
 *
 * Run with:
 *
 *   dlv_rsig file1 [file2 ...]
 *
 * The program will output the target program to the console. To store the
 * target program in a file, use redirection. For example, to parse files
 * "main-file.lp" and "extra-file.lp" and store the result in file
 * "parsed.lp", use:
 *
 *   dlv_rsig main-file.lp extra-file.lp > parsed.lp
 *
 *
 * Example RSig files
 * ==================
 *
 *-------------------------------------

%Example: cycle through negation
%
p(1). p(2). p(3). p(4).

#sig a(p),b(p).

a(X) :- not b(X).
b(X) :- not a(X).

 *-------------------------------------

%Example: lists and disjunction
%
#include <ListAndSet>

#sig a(p),b(p).

p([1]).
p([1,2]).
p([1,2,3]).

a(X) v b(X).

 *-------------------------------------
 *   
 *
 *   History
 *  ~~~~~~~~~
 *   05/02/17 - [1.8.11] Support added for embedded Prolog rules/queries.
 *   12/12/15 - [1.8.10] Outputting of infix terms corrected. Parentheses
 *                       have to be added to ensure operator priorities
 *                       are respected.
 *   10/21/15 - [1.8.9] Added ** for power and div for integer division
 *                      (for numerical constraints).
 *   10/03/15 - [1.8.8] Added:
 *                         #begin_verbatim_block.
 *                         #end_verbatim_block.
 *                      to delimit a block that should be loaded verbatim.
 *                      Each line is stored separately as a "directive".
 *                      Added special directive #verbatim. The rest of
 *                      the line following "#verbatim " is stored
 *                      verbatim as a "directive". The substring
 *                      "#verbatim " is not stored.
 *   09/30/15 - [1.8.7] Added recognition of $-prefixed MIP/LP
 *                      operators from B-Prolog.
 *   02/15/13 - [1.8.6] Added recognition of "E is E" for Prolog
 *                      code in ezcsp's defined part.
 *   06/20/11 - [1.8.5] dlv_rsig can now be compiled for Windows
 *                      using mingw.
 *   03/14/11 - [1.8.4] Added support for #mod (gringo syntax).
 *   03/01/11 - [1.8.3] Corrected handling of (+,-) and (*,/,mod).
 *   02/07/11 - [1.8.1] Reified csp operator precedence corrected.
 *                      Recognizing [#]-> and [#]<- as Sicstus'
 *                      CLP implication.
 *                      VERSIONING OF DLV_RSIG AND PARSER.C UNIFIED.
 *   11/01/10 - [1.8.0] Improved packaging for public release. Version bumped
 *                      for compatibility with parser.h's version.
 *   07/31/09 - [1.5] Added aliases for reified csp constraint operators
 *                    (e.g. \/ for #\/, /\ for #/\).
 *   07/29/09 - [1.4] Support for reified constraints added in parser.
 *                    Outputting code in parser modified to limit
 *                    unnecessary parentheses.
 *   11/03/08 - [1.3] Common code separated out as a library.
 *   11/03/08 - [1.2] Parser entirely rewritten from principled foundations.
 *                    Rewritten code is shared with EZCSP's pre-parser.
 *   10/24/08 - [1.1] Added the ability to deal with infix notation.
 *   07/21/08 - First version.
 *
 */

#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <string.h>

#include "parser.h"

/* debug flags */
#ifdef DEVEL_VERSION
#  define DEBUG_TREE 1
#endif

int main(int argc,char *argv[])
{	struct node *program,*n;

	int n_files;
	char **files;

	fprintf(stderr,"dlv_rsig version %s...\n",parser_version());

	if (argc<=1 || strcmp(argv[1],"-h")==0 || (argc>2 && strcmp(argv[1],"--")==0))
	{	printf("Usage:\n");
		printf("       dlv_rsig --     processes input from console (CTRL+D to terminate input on Unix)\n");
		printf("       dlv_rsig <file1> [<file2> [...]]    processes input files file1,file2,...\n");
		printf("       dlv_rsig -h     prints this help\n\n");

		exit(1);
	}

	if (strcmp(argv[1],"--")==0)
	{	n_files=1;
		files=NULL;
	}
	else
	{	n_files=argc-1;
		files=&argv[1];
	}

#ifdef DEVEL_VERSION
	set_debug_parse(1);	// debug parsing steps
#endif

	program=parse_program(n_files,files);

/*
  Alternative for the next block of code:

#ifdef DEBUG_TREE
	debug_show_program(program);
#endif
	add_domains_to_program(program);
	output_program(program);

 */
	for(n=program->next;n!=NULL;n=n->next)
	{	
#ifdef DEBUG_TREE
		debug_show_rule(n->data);
#endif

		add_domains_to_rule(n->data);

		output_rule(n->data);
	}

	exit(0);
}

