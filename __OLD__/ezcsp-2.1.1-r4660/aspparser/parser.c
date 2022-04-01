/*
 *
 * by Marcello Balduccini (marcello.balduccini@gmail.com)
 *
 * Copyright (C) 2009-2015 Marcello Balduccini. All Rights Reserved.
 *
 * ASP parser supporting lparse-style and dlv-style syntax, and
 * allowing to specify sorts for the arguments of relations and functions
 * in ASP programs.
 *
 * Supported syntax:
 *   1) Disjunctive rules are allowed (a(X) v b(X) v ...).
 *   2) Anonymouse variables (i.e. "_") are allowed.
 *   3) Default and strong negations are allowed (even in combination).
 *   4) Built-in dlv relations, such as #succ, are allowed.
 *   5) Lists are allowed.
 *   6) Aggregates are allowed.
 *   7) dlv-style declarations, such as #include <ListAndSet>, are allowed.
 *   8) cr-rule name (e.g. "r1:") and cr-rule connective "+-".
 *
 *   *) Lparse constraint atoms.
 *   *) Infix operators and relations.
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
 *-------------------------------------
 *  
 *
 *   History
 *  ~~~~~~~~~
 *   02/07/11 ---------- VERSIONING OF DLV_RSIG AND PARSER.C UNIFIED ----------
 *   11/04/09 - [1.7.2] Added support for reified negation (#!).
 *   10/02/09 - [1.7.1] Functions makeitem() and maketerm() exposed.
 *                      Version numbering scheme changed.
 *   07/31/09 - [1.7] Added aliases for reified csp constraint operators
 *                    (e.g. \/ for #\/, /\ for #/\).
 *   07/29/09 - [1.6] Added support for reified csp constraint operators
 *                    (#\/, #/\, etc.).
 *                    Factor (F) now is resolved to (BigE) instead of (E).
 *                    In the outputting functions, made an effort to limit
 *                    the outputting of extra parentheses (e.g. ((x))),
 *                    as lparse gives error in a few situations.
 *   05/20/09 - [1.5] Added support of cr-rule connective "+-".
 *   11/18/08 - [1.4] Added displaying of location of errors (file, line).
 *   11/03/08 - [1.3] Common code separated out from dlv_rsig.c as a library.
 *   11/03/08 - [1.2] First version of the parser based on principled foundations.
 *                    Code is shared with EZCSP's pre-parser.
 * 
 */

#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <string.h>

/* debug flags */
int DEBUG_PARSE=0;
//#define DEBUG_DOMAIN_DECL 1
//#define DEBUG_RULE 1

#include "parser.h"

#define MAX_ARITY 1024
#define MAX_HEAD 1024
#define MAX_BODY MAX_HEAD

#define MAX_DOMAINS_BUFF 10240
#define MAX_STATEMENT_LEN 10240

#define MAX_RSIGS 1024

#define RSIG_DECL "sig"

/* debugging support */
#include <stdarg.h>

int indent=0;

void IN(char *fmt,...)
{	va_list ap;
	int i;

	if (DEBUG_PARSE)
	{	for(i=0;i<indent;i++) printf(" ");
		va_start(ap,fmt);
		vprintf(fmt,ap);
		va_end(ap);
	}
	indent+=2;
}

void OUT(char *fmt,...)
{	va_list ap;
	int i;

	if (DEBUG_PARSE)
	{	for(i=0;i<indent;i++) printf(" ");
		va_start(ap,fmt);
		vprintf(fmt,ap);
		va_end(ap);
	}

	indent-=2;
}

void set_debug_parse(int truth)
{	DEBUG_PARSE=truth;
}
/* */

int n_rsigs=0;
struct item *rsigs[MAX_RSIGS];

char *curr_file=NULL;
FILE *reading_fp;
char *buff_start;
int buffer_curr_line=1;
int to_read;

char *rule_connectives[]=
{ ":-", ":~", "+-", NULL};
int rule_types[]=
{ RULE_REGULAR, RULE_SOFT_CONSTRAINT, RULE_CR_RULE, -1 };
int empty_body_ok[]=
{ 0, 0, 1, -1 };

char *error_position(char *str)
{	static char msg[10240];
	int i,count;

	/* compute the current line */
	count=buffer_curr_line;
	for(i=0;&buff_start[i]<str;i++) if (buff_start[i]=='\n') count++;

	sprintf(msg,"%s, line %d",curr_file,count);

	return(msg);
}

void make_char_available(char *str,int pos)
{	pos+=str-buff_start;

	while(to_read<=pos)
	{	if (to_read>=MAX_STATEMENT_LEN)
		{	printf("ERROR!!! MAX STATEMENT LENGTH OF %d EXCEEDED!!\n",MAX_STATEMENT_LEN);
			exit(1);
		}

		if (fread(&buff_start[to_read],sizeof(char),1,reading_fp)<=0)
		{	int i;

			for(i=to_read;i<=pos;i++) buff_start[i]=0;
		
			break;
		}

		to_read++;

	}
	buff_start[to_read]=0;
}

struct item *makeitem(int arity)
{	struct item *i;

	i=calloc(1,sizeof(struct item));
	i->arity=arity;

	if (arity>0) i->args=calloc(arity,sizeof(struct item *));

	return(i);
}

struct item *maketerm(int arity)
{	struct item *t;

	t=makeitem(arity);
	t->is_term=1;

	return(t);
}

int isCommentStart(char *str)
{	if (*str=='%') return(1);

	make_char_available(str,1);
	if (strncmp(str,"/*",2)==0) return(1);

	return(0);
}

char *skipComments(char *str)
{	if (isCommentStart(str))
	{	if (*str=='%')
		{	make_char_available(str,1);
			str++;

			while(*str!='\n' && *str!='\r') { make_char_available(str,1); str++; }
		}
		else
		{	/* then it is C-style comment */

			make_char_available(str,3);	/* the chars we are skipping plus room for the end-of-comment delimiter */
			str+=2;
			while(strncmp(str,"*/",2)!=0) { make_char_available(str,2); str++; }
			make_char_available(str,2);
			str+=2;
		}

		while(isspace((int)*str)) { make_char_available(str,1); str++; }
	}

	return(str);
}

char *skipBlanks(char *str)
{	while(isspace((int)*str) || (isCommentStart(str)))
	{	while(isspace((int)*str)) { make_char_available(str,1); str++; }

		str=skipComments(str);
	}


	return(str);
}

char *skipCRLFs(char *str)
{	while(*str=='\r' || *str=='\n')
	{	make_char_available(str,1);
		str++;
	}


	return(str);
}

char *recognizeSingleChar(char *str,char c)
{	if (str==NULL) return(NULL);

	IN("recognizeSingleChar('%s','%c')\n",str,c);

	str=skipBlanks(str);

	if (*str==c)
	{
		make_char_available(str,1);

		OUT("SUCCESS\n");

		return(str+1);
	}

	OUT("FAIL\n");
	return(NULL);
}

#define recognizeOpenParen(str) recognizeSingleChar(str,'(')
#define recognizeCloseParen(str) recognizeSingleChar(str,')')

#define recognizeOpenCurly(str) recognizeSingleChar(str,'{')
#define recognizeCloseCurly(str) recognizeSingleChar(str,'}')

#define recognizeOpenBracket(str) recognizeSingleChar(str,'[')
#define recognizeCloseBracket(str) recognizeSingleChar(str,']')

char *recognizeWord(char *str,char *c)
{	if (str==NULL) return(NULL);

	IN("recognizeWord(%s=?%s)\n",str,c);

	str=skipBlanks(str);

	make_char_available(str,strlen(c)+1);

	if (strncasecmp(str,c,strlen(c))!=0)
	{
		OUT("FAIL\n");
		return(NULL);
	}

	if (isalnum((int)str[strlen(c)]))	// make sure this is a whole word
	{
		OUT("FAIL\n");
		return(NULL);
	}

	return(&str[strlen(c)]);
}

#define recognizeNot(str) recognizeWord(str,"not")

char *recognizeDelimitedString(char *str,char d_start,char d_end,int allow_comments,struct item **i)
{	char *start_ptr;
	struct item *a;

	if (str==NULL) return(NULL);

	IN("recognizeDelimitedString(%c->%c,%s)\n",d_start,d_end,str);

	start_ptr=str;
	str=recognizeSingleChar(str,d_start);
	if (str==NULL)
	{
		OUT("FAIL\n");
		return(NULL);
	}

	if (allow_comments) str=skipComments(str);
	while(*str && *str!=d_end)
	{	make_char_available(str,1);
		str++;

		if (allow_comments) str=skipComments(str);
	}
	if (*str==0)
	{
		OUT("FAIL\n");
		return(NULL);
	}

	make_char_available(str,1);
	str++;

	a=makeitem(0);
	a->relation=calloc(str-start_ptr+1,sizeof(char));
	strncpy(a->relation,start_ptr,str-start_ptr);
	*i=a;

	OUT("SUCCESS\n");

	return(str);
}

char *recognizeOP(char *str,struct item **i,char **ops)
{	struct item *op;

	int j;
	int match,max_matching_len;

	if (str==NULL) return(NULL);

	IN("recognizeOP(%s)\n",str);

	str=skipBlanks(str);

	match=-1;
	max_matching_len=0;
	for(j=0;ops[j];j++)
	{	make_char_available(str,strlen(ops[j]));

		if ((strlen(ops[j])>max_matching_len) &&
		    (strncmp(str,ops[j],strlen(ops[j]))==0))
		{	match=j;
			max_matching_len=strlen(ops[j]);
		}
	}

	if (match==-1)
	{
		OUT("FAIL\n");
		return(NULL);
	}

	str=&str[max_matching_len];

	op=makeitem(0);
	op->relation=strdup(ops[match]);

	*i=op;

	OUT("SUCCESS\n");
	return(str);
}

char *recognizeOP_highPrec(char *str,struct item **i)
{	static char *ops[]=
	{	">", "#>", "$>",
		"<", "#<", "$<",
		">=", "#>=", "$>=",
		"<=", "#<=", "$<=", "=<", "#=<", "$=<",
		"==", "#==", "$==", "=", "#=", "$=",
		"!=", "#!=", "$!=", "\\=", "#\\=", "$\\=", "is", 

		NULL
	};

	IN("recognizeOP_highPrec(%s)\n",str);

	str=recognizeOP(str,i,ops);

	OUT("whatever recognizeOP returned\n");

	return(str);
}

char *recognizeOP_lowPrec(char *str,struct item **i)
{	static char *ops[]=
	{	"#!",
		"\\/", "#\\/", "$\\/",
		"/\\", "#/\\", "$/\\",
		"\\", "#\\", "$\\",
		"->", "#->", "$->",
		"<-", "#<-", "$<-",
		"<=>", "#<=>", "$<=>",

		NULL
	};

	IN("recognizeOP_lowPrec(%s)\n",str);

	str=recognizeOP(str,i,ops);

	OUT("whatever recognizeOP returned\n");

	return(str);
}

char *recognizeMultiCharOP(char *str,struct item **i)
{	char *str2;

	IN("recognizeMultiCharOP(%s)\n",str);

	str2=recognizeOP_highPrec(str,i);
	if (str2)
	{
		OUT("SUCCESS\n");
		return(str2);
	}

	str2=recognizeOP_lowPrec(str,i);
	if (str2)
	{
		OUT("SUCCESS\n");
		return(str2);
	}

	OUT("FAIL\n");

	return(NULL);
}

char *recognizeVariable(char *str,struct item **i)
{	struct item *v;
	int j;

	if (str==NULL) return(NULL);

	IN("recognizeVariable(%s)\n",str);

	str=skipBlanks(str);

	if ((*str=='_') || (isalnum((int)*str) && isupper((int)*str)))
	{	make_char_available(str,1);
		for(j=1;isalnum((int)str[j]) || str[j]=='_';make_char_available(str,j+1),j++);

		v=maketerm(0);
		v->relation=calloc(j+1,sizeof(char));
		strncpy(v->relation,str,j);
		v->is_variable=1;

		*i=v;

		OUT("SUCCESS\n");
		return(&str[j]);
	}

	OUT("FAIL\n");

	return(NULL);
}

char *recognizeNumber(char *str,struct item **i)
{	struct item *v;
	int j;

	if (str==NULL) return(NULL);

	IN("recognizeNumber(%s)\n",str);

	str=skipBlanks(str);

	make_char_available(str,1);
	if (isdigit((int)*str) || (*str=='-' && isdigit((int)str[1])))
	{	make_char_available(str,1);
		for(j=1;isdigit((int)str[j]) || (str[j]=='.' && isdigit((int)str[j+1]));make_char_available(str,j+1),j++);

		if (isalpha((int)str[j]))	// no letters after the numbers
		{
			OUT("FAIL\n");
			return(NULL);
		}

		v=maketerm(0);
		v->relation=calloc(j+1,sizeof(char));
		strncpy(v->relation,str,j);

		*i=v;

		OUT("SUCCESS\n");
		return(&str[j]);
	}

	OUT("FAIL\n");

	return(NULL);
}

char *recognizeFunctionSymbol(char *str,struct item **i)
{	struct item *f;
	char *str2;
	int j;

	if (str==NULL) return(NULL);

	IN("recognizeFunctionSymbol(%s)\n",str);

	str=skipBlanks(str);

	/* first check for quote-delimited strings */
	if (*str=='\"')
	{	make_char_available(str,1);
		for(j=1;str[j] && str[j]!='\"';make_char_available(str,j+1),j++);

		if (str[j]==0)
		{
			OUT("FAIL\n");
			return(NULL);
		}
		
		make_char_available(str,j+1);
		j++;
	}
	else
	/* the following case is needed for e.g. "<=" in sum[x/2],<=,100 */
	if ((str2=recognizeOP_highPrec(str,i)))
	{	(*i)->is_term=1;
		(*i)->is_infix=0;

		OUT("SUCCESS\n");
		return(str2);
	}
	else
	if ((isalnum((int)*str) && islower((int)*str)) ||
	    (*str=='#'))	/* dlv-style built-in functions, e.g. #count */
	{	make_char_available(str,1);
		for(j=1;isalnum((int)str[j]) || str[j]=='_';make_char_available(str,j+1),j++);
	}
	else
	{
		OUT("FAIL\n");
		return(NULL);
	}

	f=maketerm(0);
	f->relation=calloc(j+1,sizeof(char));
	strncpy(f->relation,str,j);

	*i=f;

	OUT("SUCCESS\n");

	return(&str[j]);
}


char *recognizeRelationSymbol(char *str,struct item **i)
{	struct item *f;
	int j;

	if (str==NULL) return(NULL);

	IN("recognizeRelationSymbol(%s)\n",str);

	str=skipBlanks(str);

	/* first check for quote-delimited strings */
	if (*str=='\"')
	{	make_char_available(str,1);
		for(j=1;str[j] && str[j]!='\"';make_char_available(str,j+1),j++);

		if (str[j]==0)
		{
			OUT("FAIL\n");
			return(NULL);
		}

		make_char_available(str,j+1);
		j++;
	}
	else
	if ((isalnum((int)*str) && islower((int)*str)) ||
	    (*str=='#'))	/* dlv-style built-in relations, e.g. #int */
	{	make_char_available(str,1);
		for(j=1;isalnum((int)str[j]) || str[j]=='_';make_char_available(str,j+1),j++);
	}
	else
	{
		OUT("FAIL\n");
		return(NULL);
	}
	
	f=maketerm(0);
	f->relation=calloc(j+1,sizeof(char));
	strncpy(f->relation,str,j);

	*i=f;

	OUT("SUCCESS\n");

	return(&str[j]);
}

/* Term ::= Variable | Number | FunctionSymbol | FunctionSymbol(CommaList) | FunctionSymbol{String} | [ CommaList ] */
char *recognizeTerm(char *str,struct item **i)
{	char *str2,*str3;
	char *recognizeAndFillCommaList(char *str,struct item *i);
	char *recognizeBasicLit(char *str,struct item **i);
	char *recognizeE(char *str,struct item **i);
	struct item *a;

	if (str==NULL) return(NULL);

	IN("recognizeTerm(%s)\n",str);

	str2=recognizeVariable(str,i);
	if (str2)
	{	
		OUT("SUCCESS\n");
		return(str2);
	}

	str2=recognizeNumber(str,i);
	if (str2)
	{	
		OUT("SUCCESS\n");
		return(str2);
	}

	a=maketerm(0);
	str2=recognizeCloseBracket(recognizeAndFillCommaList(recognizeOpenBracket(str),a));
	if (str2)
	{	a->relation=strdup("[");
		a->is_parenthesis=1;
		a->arglist_end=']';

		*i=a;

		OUT("SUCCESS\n");
		return(str2);
	}
	free(a);

	str2=recognizeFunctionSymbol(str,i);
	if (str2==NULL)
	{
		OUT("FAIL\n");
		return(NULL);
	}

	str3=recognizeCloseParen(recognizeAndFillCommaList(recognizeOpenParen(str2),*i));

	if (str3)
	{
		OUT("SUCCESS\n");
		return(str3);
	}

	str3=recognizeDelimitedString(str2,'{','}',1,&a);

	if (str3)
	{
		OUT("SUCCESS\n");

		(*i)->arity=1;
		(*i)->args=calloc(1,sizeof(struct item *));
		(*i)->args[0]=a;
		(*i)->skip_parentheses=1;

		return(str3);
	}

	if (str2)
	{
		OUT("SUCCESS\n");
	}
	else
	{
		OUT("FAIL\n");
	}

	return(str2);
}

/*  SmallF ::= ( BiggerE ) | Term */
char *recognizeSmallF(char *str,struct item **i)
{	char *str2;
	char *recognizeBiggerE(char *str,struct item **i);

	if (str==NULL) return(NULL);

	IN("recognizeSmallF(%s)\n",str);

	str2=recognizeCloseParen(recognizeBiggerE(recognizeOpenParen(str),i));
	if (str2)
	{	struct item *a;

		a=maketerm(1);
		a->relation=strdup("(");
		a->is_parenthesis=1;
		a->arglist_end=')';
		a->args[0]=*i;

		*i=a;

		OUT("SUCCESS\n");

		return(str2);
	}

	str=recognizeTerm(str,i);

	OUT("whatever recognizeTerm returned\n");

	return(str);
}

/*  F ::= -SmallF | ?- SmallF | ?-SmallF | #?- SmallF | #?-SmallF | SmallF */
char *recognizeF(char *str,struct item **i)
{	char *str2,*str3;
	int found;
	struct item *j;

	static char *ops[]=
	{	"?-", "#?-",

		NULL
	};

	IN("recognizeF(%s)\n",str);

	found=0;
	if ((str2=recognizeSingleChar(str,'-')) && (skipBlanks(str2)==str2) && (str3=recognizeSmallF(str2,i)))
		found=1;
	else
	if ((str2=recognizeOP(str,&j,ops)) && (str3=skipBlanks(str2)) && (str3=recognizeSmallF(str3,i)))
	{	free(j->relation);
		free(j);
		found=1;
	}

	if (found)
	{	struct item *a;
		int l;

		str=skipBlanks(str);
		l=str2-str;
		a=maketerm(1);
		a->relation=calloc(l+1,sizeof(char));
		strncpy(a->relation,str,l);
		a->args[0]=*i;
		a->skip_parentheses=((*i)->arity == 0);	/* If arity of the arg is 0, skip parens when outputting */

		*i=a;

		OUT("SUCCESS\n");

		return(str3);
	}

	str=recognizeSmallF(str,i);

	OUT("whatever recognizeSmallF returned\n");

	return(str);
}

/*  Exp ::= F | F ** Exp */
char *recognizeExp(char *str,struct item **i)
{	static char *ops[]=
	{	"**",

		NULL
	};
	char *str2,*str3;
	struct item *a,*b,*op,*j;
	char *c;

	if (str==NULL) return(NULL);

	IN("recognizeExp(%s)\n",str);

	str2=recognizeF(str,&a);
	if (str2==NULL)
	{
		OUT("FAIL\n");
		return(NULL);
	}

	*i=a;

	b=NULL;

	if ((str3=recognizeOP(str2,&b,ops))==0)
	{	OUT("SUCCESS\n");
		return(str2);
	}

	c=ops[0];

	if (b!=NULL)
	{	free(b);
		b=NULL;
	}

	str3=recognizeExp(str3,&b);
	if (str3==NULL)
	{
		OUT("SUCCESS\n");
		return(str2);
	}

	if (strcmp(b->relation,c)==0)
	{
		for(j=b;
		    strcmp(j->args[0]->relation,c)==0;
		    j=j->args[0]);

		op=maketerm(2);
		op->is_infix=1;
		op->relation=strdup("**");
		op->args[0]=a;
		op->args[1]=j->args[0];
		j->args[0]=op;
		op=b;
	}
	else
	{	op=maketerm(2);
		op->is_infix=1;
		op->relation=strdup("**");
		op->args[0]=a;
		op->args[1]=b;
	}

	*i=op;

	OUT("SUCCESS\n");

	return(str3);
}

/*  T ::= Exp | Exp * T | Exp / T  | Exp div T | Exp mod T | Exp #mod T */
char *recognizeT(char *str,struct item **i)
{	char *str2,*str3;
	struct item *a,*b,*op,*j;
	char *c;

	if (str==NULL) return(NULL);

	IN("recognizeT(%s)\n",str);

	str2=recognizeExp(str,&a);
	if (str2==NULL)
	{
		OUT("FAIL\n");
		return(NULL);
	}

	*i=a;

	b=NULL;
	if ((str3=recognizeSingleChar(str2,'*')) && !recognizeMultiCharOP(str2,&b))
		c="*";
	else
	if ((str3=recognizeSingleChar(str2,'/')) && !recognizeMultiCharOP(str2,&b))
		c="/";
	else
	if ((str3=recognizeWord(str2,"div")))
		c="div";
	else
	if ((str3=recognizeWord(str2,"mod")))
		c="mod";
	else
	if ((str3=recognizeWord(str2,"#mod")))
		c="#mod";
	else
	{
		OUT("SUCCESS\n");
		return(str2);
	}

	if (b!=NULL)
	{	free(b);
		b=NULL;
	}

	str3=recognizeT(str3,&b);
	if (str3==NULL)
	{
		OUT("SUCCESS\n");
		return(str2);
	}

	if (strcmp(b->relation,"*")==0 || strcmp(b->relation,"/")==0 ||
	    strcmp(b->relation,"div")==0 || strcmp(b->relation,"mod")==0 || 
	    strcmp(b->relation,"#mod")==0)
	{
		for(j=b;
		    strcmp(j->args[0]->relation,"*")==0 || 
		      strcmp(j->args[0]->relation,"/")==0 || 
		      strcmp(j->args[0]->relation,"div")==0 ||
		      strcmp(j->args[0]->relation,"mod")==0 ||
		      strcmp(j->args[0]->relation,"#mod")==0;j=j->args[0]);

		op=maketerm(2);
		op->is_infix=1;
		op->relation=strdup(c);
		op->args[0]=a;
		op->args[1]=j->args[0];
		j->args[0]=op;
		op=b;
	}
	else
	{	op=maketerm(2);
		op->is_infix=1;
		op->relation=strdup(c);
		op->args[0]=a;
		op->args[1]=b;
	}

	*i=op;

	OUT("SUCCESS\n");

	return(str3);
}

/*  E ::= T | T + E | T - E */
char *recognizeE(char *str,struct item **i)
{	char *str2,*str3;
	struct item *a,*b,*op,*j;
	char c;

	if (str==NULL) return(NULL);

	IN("recognizeE(%s)\n",str);

	str2=recognizeT(str,&a);
	if (str2==NULL)
	{
		OUT("FAIL\n");
		return(NULL);
	}

	*i=a;

	b=NULL;
	if ((str3=recognizeSingleChar(str2,'+')) && !recognizeMultiCharOP(str2,&b))
		c='+';
	else
	if ((str3=recognizeSingleChar(str2,'-')) && !recognizeMultiCharOP(str2,&b))
		c='-';
	else
	{
		OUT("SUCCESS\n");
		return(str2);
	}

	if (b!=NULL)
	{	free(b);
		b=NULL;
	}

	str3=recognizeE(str3,&b);
	if (str3==NULL)
	{
		OUT("SUCCESS\n");
		return(str2);
	}

	if (strcmp(b->relation,"+")==0 || strcmp(b->relation,"-")==0)
	{	
		for(j=b;strcmp(j->args[0]->relation,"+")==0 || strcmp(j->args[0]->relation,"-")==0;j=j->args[0]);
	
		op=maketerm(2);
		op->is_infix=1;
		op->relation=calloc(2,sizeof(char));
		op->relation[0]=c;
		op->args[0]=a;
		op->args[1]=j->args[0];
		j->args[0]=op;
		op=b;
	}
	else
	{	op=maketerm(2);
		op->is_infix=1;
		op->relation=calloc(2,sizeof(char));
		op->relation[0]=c;
		op->args[0]=a;
		op->args[1]=b;
	}

	*i=op;

	OUT("SUCCESS\n");

	return(str3);
}

///*  BigE ::= E OP_highPrec BigE | E */
/*  BigE ::= InfixAtom | E */
char *recognizeBigE(char *str,struct item **i)
{	char *str2;

	char *recognizeInfixAtom(char *str,struct item **i);

	if (str==NULL) return(NULL);

	IN("recognizeBigE(%s)\n",str);

	str2=recognizeInfixAtom(str,i);
	if (str2!=NULL)
	{
		OUT("SUCCESS\n");
		return(str2);
	}

	str2=recognizeE(str,i);

	OUT("whatever recognizeE returned\n");

	return(str2);
}


/*  BiggerE ::= BigE OP_lowPrec BiggerE | BigE */
char *recognizeBiggerE(char *str,struct item **i)
{	char *str2,*str3;
	struct item *a,*b,*op;

	if (str==NULL) return(NULL);

	IN("recognizeBiggerE(%s)\n",str);

	str2=recognizeBigE(str,&a);
	if (str2==NULL)
	{
		OUT("FAIL\n");
		return(NULL);
	}

	*i=a;

	str3=recognizeOP_lowPrec(str2,&op);
	if (str3==NULL)
	{
		OUT("SUCCESS\n");
		return(str2);
	}

	str3=recognizeBiggerE(str3,&b);
	if (str3==NULL)
	{
		OUT("SUCCESS\n");
		return(str2);
	}

	op->arity=2;
	op->is_infix=1;
	op->args=calloc(op->arity,sizeof(struct item *));
	op->args[0]=a;
	op->args[1]=b;
	*i=op;

	OUT("SUCCESS\n");

	return(str3);
}
///*  BiggerE ::= BigE OP_lowPrec BiggerE | BigE */
/*
char *recognizeBiggerE(char *str,struct item **i)
{	char *str2,*str3;
	struct item *a,*b,*op;

	if (str==NULL) return(NULL);

	IN("recognizeBiggerE(%s)\n",str);

	str2=recognizeBigE(str,&a);
	if (str2==NULL)
	{
		OUT("FAIL\n");
		return(NULL);
	}

	*i=a;

	str3=recognizeOP_lowPrec(str2,&op);
	if (str3==NULL)
	{
		OUT("SUCCESS\n");
		return(str2);
	}

	str3=recognizeBiggerE(str3,&b);
	if (str3==NULL)
	{
		OUT("FAIL\n");
		return(NULL);
	}

	op->arity=2;
	op->is_infix=1;
	op->args=calloc(op->arity,sizeof(struct item *));
	op->args[0]=a;
	op->args[1]=b;
	*i=op;

	OUT("SUCCESS\n");

	return(str3);
}
*/

/* CommaList ::= BiggerE | BiggerE, CommaList */
char *recognizeCommaList(char *str,struct item **i)
{	struct item *a,*b,*l;
	char *str2;

	if (str==NULL) return(NULL);

	IN("recognizeCommaList(%s)\n",str);

	str=recognizeBiggerE(str,&a);
	if (str==NULL)
	{	
		OUT("FAIL\n");
		return(NULL);
	}


	str2=recognizeCommaList(recognizeSingleChar(str,','),&b);
	if (str2==NULL)
	{
		*i=a;
		
		OUT("SUCCESS\n");

		return(str);
	}

	l=maketerm(2);
	l->relation=strdup(",");
	l->is_infix=0;
	l->skip_parentheses=0;
	l->args[0]=a;
	l->args[1]=b;

	*i=l;
	
	OUT("SUCCESS\n");

	return(str2);
}

/* SemicolonList ::= BiggerE | BiggerE; SemicolonList */
char *recognizeSemicolonList(char *str,struct item **i)
{	struct item *a,*b,*l;
	char *str2;

	if (str==NULL) return(NULL);

	IN("recognizeSemicolonList(%s)\n",str);

	str=recognizeBiggerE(str,&a);
	if (str==NULL)
	{	
		OUT("FAIL\n");
		return(NULL);
	}


	str2=recognizeSemicolonList(recognizeSingleChar(str,';'),&b);
	if (str2==NULL)
	{
		*i=a;
		
		OUT("SUCCESS\n");

		return(str);
	}

	l=maketerm(2);
	l->relation=strdup(";");
	l->is_infix=1;
	l->skip_parentheses=1;
	l->args[0]=a;
	l->args[1]=b;

	*i=l;
	
	OUT("SUCCESS\n");

	return(str2);
}

/* ExprList ::= BiggerE .. BiggerE | SemicolonList */
char *recognizeExprList(char *str,struct item **i)
{	char *str2;
	struct item *arg1,*arg2;

	if (str==NULL) return(NULL);

	IN("recognizeExprList(%s)\n",str);

	str2=recognizeBiggerE(recognizeSingleChar(recognizeSingleChar(recognizeBiggerE(str,&arg1),'.'),'.'),&arg2);
	if (str2)
	{	struct item *a;

		a=maketerm(2);
		a->relation=strdup("..");
		a->is_infix=1;
		a->skip_parentheses=1;
		a->args[0]=arg1;
		a->args[1]=arg2;

		*i=a;

		OUT("SUCCESS\n");

		return(str2);
	}

	str2=recognizeSemicolonList(str,i);
	if (str2)
	{	
		OUT("SUCCESS\n");
		return(str2);
	}

	OUT("FAIL\n");

	return(NULL);
}

/* CommaList ::= ExprList | ExprList, CommaList */
char *recognizeAndFillCommaList(char *str,struct item *i)
{	char *str2;
	struct item *args[MAX_ARITY];
	struct item *arg;
	int j;

	if (str==NULL) return(NULL);

	IN("recognizeAndFillCommaList(%s)\n",str);

	for(j=0;j<i->arity;j++)
		args[j]=i->args[j];
	do
	{	/* safety check */
		if (i->arity>=MAX_ARITY)
		{	printf("ERROR!! MAXIMUM ALLOWED ARITY OF %d EXCEEDED.\n",i->arity);
			exit(1);
		}

		str2=recognizeExprList(str,&arg);
		if (str2==NULL)
		{
			OUT("FAIL\n");
			return(NULL);
		}

		args[i->arity]=arg;	/* argument */
		i->arity++;

	} while((str=recognizeSingleChar(str2,',')));

	if (i->arity>0)
	{	/* copy temp structures to permanent structures */
		if (i->args) free(i->args);
		i->args=calloc(i->arity,sizeof(struct item *));
		for(j=0;j<i->arity;j++) i->args[j]=args[j];
	}

	OUT("SUCCESS\n");

	return(str2);	/* pointer after the end of the last E found */
}

///* InfixAtom ::= BiggerE */
/*
char *recognizeInfixAtom(char *str,struct item **i)
{	if (str==NULL) return(NULL);

	IN("recognizeInfixAtom(%s) -> recognizeBiggerE\n",str);

	str=recognizeBiggerE(str,i);

	OUT("whatever recognizeBiggerE returned\n");
	
	return(str);
}
*/
/*  InfixAtom ::= E OP_highPrec BigE | E #:- CommaList */
char *recognizeInfixAtom(char *str,struct item **i)
{	char *str2,*str3;
	struct item *a,*b,*op;

	if (str==NULL) return(NULL);

	IN("recognizeInfixAtom(%s)\n",str);

	str2=recognizeE(str,&a);
	if (str2==NULL)
	{
		OUT("FAIL\n");
		return(NULL);
	}

	*i=a;

	str3=recognizeOP_highPrec(str2,&op);
	if (str3)
	{	str3=recognizeBigE(str3,&b);
		if (str3==NULL)
		{
			OUT("FAIL\n");
			return(NULL);
		}

		op->arity=2;
		op->is_infix=1;
		op->args=calloc(op->arity,sizeof(struct item *));
		op->args[0]=a;
		op->args[1]=b;
		*i=op;

		OUT("SUCCESS\n");

		return(str3);
	}

	static char *ops[]=
	{	"#:-",

		NULL
	};
	str2=recognizeOP(str2,&op,ops);
	if (str2==NULL)
	{
		OUT("FAIL\n");
		return(NULL);
	}

	b=maketerm(0);
//	b->relation=strdup("#,");
	b->relation=strdup("[");
	b->is_parenthesis=1;
	b->arglist_end=']';
	str3=recognizeAndFillCommaList(str2,b);
	if (str3==NULL)
	{
		OUT("FAIL\n");
		return(NULL);
	}

	op->is_infix=1;
	op->arity=2;
	op->args=calloc(op->arity,sizeof(struct item *));
	op->args[0]=a;
	op->args[1]=b;
	*i=op;

	OUT("SUCCESS\n");

	return(str3);
}
/*
char *recognizeInfixAtom(char *str,struct item **i)
{	char *str2;
	struct item *a,*b,*op;

	if (str==NULL) return(NULL);

	IN("recognizeInfixAtom(%s)\n",str);

	str2=recognizeE(str,&a);
	if (str2==NULL)
	{
		OUT("FAIL\n");
		return(NULL);
	}

	*i=a;

	str2=recognizeOP_highPrec(str2,&op);
	if (str2==NULL)
	{
		OUT("FAIL\n");
		return(NULL);
	}

	str2=recognizeBigE(str2,&b);
	if (str2==NULL)
	{
		OUT("FAIL\n");
		return(NULL);
	}

	op->arity=2;
	op->is_infix=1;
	op->args=calloc(op->arity,sizeof(struct item *));
	op->args[0]=a;
	op->args[1]=b;
	*i=op;

	OUT("SUCCESS\n");

	return(str2);
}
*/
///* InfixAtom ::= E OP InfixAtom | E OP E */
/*
char *recognizeInfixAtom(char *str,struct item **i)
{	char *str2,*str3;
	struct item *a,*b,*op;

	if (str==NULL) return(NULL);

	IN("recognizeInfixAtom(%s)\n",str);

	str2=recognizeE(str,&a);
	if (str2==NULL)
	{
		OUT("FAIL\n");
		return(NULL);
	}

	str2=recognizeOP(str2,&op);
	if (str2==NULL)
	{
		OUT("FAIL\n");
		return(NULL);
	}

	str3=recognizeInfixAtom(str2,&b);
	if (str3==NULL)
		str3=recognizeE(str2,&b);

	if (str3==NULL)
	{
		OUT("FAIL\n");
		return(NULL);
	}

	op->arity=2;
	op->is_infix=1;
	op->args=calloc(op->arity,sizeof(struct item *));
	op->args[0]=a;
	op->args[1]=b;
	*i=op;

	OUT("SUCCESS\n");

	return(str3);
}
*/

/* Atom ::= RelationSymbol | RelationSymbol(CommaList) */
char *recognizeAtom(char *str,struct item **i)
{	char *str2,*str3;

	if (str==NULL) return(NULL);

	IN("recognizeAtom(%s)\n",str);

	str2=recognizeRelationSymbol(str,i);
	if (str2==NULL)
	{
		OUT("FAIL\n");
		return(NULL);
	}

	str3=recognizeCloseParen(recognizeAndFillCommaList(recognizeOpenParen(str2),*i));
	if (str3)
		str2=str3;

	OUT("whatever recognizeCloseParen(recognizeAndFillCommaList(recognizeOpenParen())) returned\n");
	return(str2);
}

/* ConstraintLiteral ::= E { String } E | { String } E | E { String } */
char *recognizeConstraintLiteral(char *str,struct item **i)
{	char *str2;
	struct item *e1,*e2;

	if (str==NULL) return(NULL);

	IN("recognizeConstraintLiteral(%s)\n",str);

	str2=recognizeE(str,&e1);
	if (str2==NULL)
		e1=NULL;
	else
		str=str2;

	str=recognizeDelimitedString(str,'{','}',1,i);
	if (str==NULL)
	{
		OUT("FAIL\n");
		return(NULL);
	}

	str2=recognizeE(str,&e2);
	if (str2==NULL)
		e2=NULL;
	else
		str=str2;

	if (e1==NULL)
	{	e1=maketerm(0);
		e1->relation=strdup("");
	}
	if (e2==NULL)
	{	e2=maketerm(0);
		e2->relation=strdup("");
	}

	(*i)->is_infix=1;	// essentially, { String } is syntactically like an infix operator
	(*i)->arity=2;
	(*i)->args=calloc(2,sizeof(struct item *));
	(*i)->args[0]=e1;
	(*i)->args[1]=e2;


	OUT("SUCCESS\n");

	return(str);
}

/* BasicLit ::= -Atom | Atom */
char *recognizeBasicLit(char *str,struct item **i)
{	char *str2;
	int strongneg;

	if (str==NULL) return(NULL);

	IN("recognizeBasicLit(%s)\n",str);

	strongneg=0;

	str2=recognizeSingleChar(str,'-');
	if (str2)
	{	strongneg=1;
		str=str2;
	}

	str2=recognizeAtom(str,i);
	if (str2)
		(*i)->strong_negation=strongneg;

	OUT("whatever recognizeAtom returned\n");

	return(str2);
}

/* Lit ::= InfixAtom | ConstraintLiteral | BasicLit */
char *recognizeLit(char *str,struct item **i)
{	char *str2;

	if (str==NULL) return(NULL);

	IN("recognizeLit(%s)\n",str);

	str2=recognizeInfixAtom(str,i);
	if (str2)
	{
		OUT("SUCCESS\n");
		return(str2);
	}

	str2=recognizeConstraintLiteral(str,i);
	if (str2)
	{
		OUT("SUCCESS\n");
		return(str2);
	}

	str=recognizeBasicLit(str,i);
	OUT("whatever recognizeBasicLit returned\n");

	return(str);
}

/* ExtLit ::= not Lit | Lit */
char *recognizeExtLit(char *str,struct item **i)
{	char *str2;

	if (str==NULL) return(NULL);

	IN("recognizeExtLit(%s)\n",str);

	str2=recognizeLit(recognizeNot(str),i);
	if (str2)
	{	(*i)->default_negation=1;

		OUT("SUCCESS\n");
		return(str2);
	}

	str2=recognizeLit(str,i);
	if (str2)
	{
		OUT("SUCCESS\n");
		return(str2);
	}

	OUT("FAIL\n");

	return(NULL);
}

void debug_show_tree(int indent,struct item *a)
{	int i;

	for(i=0;i<indent;i++)
		fprintf(stderr," ");

	if (a->is_term)
		fprintf(stderr,"    TERM: FUNCTOR: \'%s\'  INFIX: %s  VARIABLE: %s\n",a->relation,(a->is_infix) ? "yes":"no",(a->is_variable) ? "yes":"no");
	else
		fprintf(stderr,"    ATOM: RELATION: \'%s\'  INFIX: %s  NOT: %s  NEG: %s\n",a->relation,(a->is_infix) ? "yes":"no",a->default_negation ? "yes":"no",a->strong_negation ? "yes":"no");

	for(i=0;i<a->arity;i++)
		debug_show_tree(indent+2,a->args[i]);
}

char *rule_connective(struct rule *r)
{	int i;

	for(i=0;rule_connectives[i]!=NULL;i++)
		if (r->type==rule_types[i])
			return(rule_connectives[i]);

	fprintf(stderr,"***INTERNAL ERROR: unexpected rule type %d\n",r->type);
	exit(1);
}

void debug_show_rule(struct rule *r)
{	int i;

	if (r->type==RULE_SYSTEM_DIRECTIVE)
	{	fprintf(stderr,"DIRECTIVE: %s\n",r->system_directive);
		return;
	}

	fprintf(stderr,"RULE\n");
	fprintf(stderr,"TYPE: %s\n",rule_connective(r));
	if (r->name!=NULL)
	{	fprintf(stderr,"  NAME:\n");
		debug_show_tree(4,r->name);
	}
	fprintf(stderr,"  HEAD:\n");
	for(i=0;i<r->head_size;i++)
		debug_show_tree(4,r->head[i]);
	fprintf(stderr,"  BODY:\n");
	for(i=0;i<r->body_size;i++)
		debug_show_tree(4,r->body[i]);
}

void debug_show_program(struct node *program)
{	struct node *n;

	for(n=program->next;n!=NULL;n=n->next)
		debug_show_rule(n->data);
}

void display_rule_connectives(void)
{	int i;

	for(i=0;rule_connectives[i]!=NULL;i++)
		printf(",'%s'",rule_connectives[i]);
}

/* returns -1 if connective not recognized; otherwise, it returns the index in the rule_connectives array. */
int which_rule_connective(char *str)
{	int i;

	for(i=0;rule_connectives[i]!=NULL;i++)
	{	make_char_available(str,strlen(rule_connectives[i])-1);
		if (strncmp(str,rule_connectives[i],strlen(rule_connectives[i]))==0)
			break;
	}

	if (rule_connectives[i]==NULL) return(-1);

	return(i);
}

/* idx is index in rule_connectives array */
int allows_empty_body(int idx)
{	return(empty_body_ok[idx]);
}

struct rule *get_rule(char *str,char **ptr_next)
{
	struct rule *r;
	struct item *a;
	struct item *head[MAX_HEAD];
	struct item *body[MAX_BODY];

	char *item_ptr_next;

	int i;
	int finished;


	str=skipBlanks(str);


	r=calloc(1,sizeof(struct rule));

	r->head_size=0;
	/* check if we have an empty head (although technically "+- f." is not a valid cr-rule. */
	finished=(which_rule_connective(str)!=-1);
	while(!finished)
	{	if (r->head_size>=MAX_HEAD)
		{	printf("ERROR: MAX HEAD SIZE OF %d EXCEEDED!\n",MAX_HEAD);
			exit(1);
		}
		item_ptr_next=recognizeExtLit(str,&a);
		if (item_ptr_next==NULL)
		{	printf("%s: SYNTAX ERROR AT: \'%s\'\n",error_position(str),str);
			return(NULL);
		}

		head[r->head_size]=a;
		r->head_size++;

		str=item_ptr_next;

		str=skipBlanks(str);

		i=which_rule_connective(str);

		/* is this the end of the NAME part of a cr-rule? */
		if (*str==':' && i==-1 && r->head_size==1)
		{	/* Move the literal from the head to the name of the rule */
			r->name=head[0];
			head[0]=NULL;
			r->head_size--;

			finished=0;
			make_char_available(str,1);
			str++;

			continue;
		}

		if (*str=='v')
		{	finished=0;

			make_char_available(str,1);
			str++;

			continue;
		}

		if (*str!='.' && i==-1)
		{	printf("%s: SYNTAX ERROR: EXPECTED ONE OF 'v', a cr-rule name, '.'",error_position(str));
			display_rule_connectives();
			printf(" AT \'%s\'\n",str);
			exit(1);
		}

		/* we found a rule connective, or . */
		finished=1;
	}

	//r->head=a;
	//ptr_start=str;

	//str=item_ptr_next;
	r->head=calloc(r->head_size,sizeof(struct item *));
	for(i=0;i<r->head_size;i++) r->head[i]=head[i];

	str=skipBlanks(str);

	/* check if body is empty */
	if (*str=='.')
	{	make_char_available(str,1);
		str++;
	}
	else
	{	int connective_idx;

		connective_idx=which_rule_connective(str);
	
		if (connective_idx==-1)
		{	printf("%s: SYNTAX ERROR: one of '.'",error_position(str));
			display_rule_connectives();
		 	printf(" EXPECTED AT \'%s\'\n",str);
			exit(1);
		}

		r->type=rule_types[connective_idx];

		make_char_available(str,strlen(rule_connectives[connective_idx]));
		str+=strlen(rule_connectives[connective_idx]);

		str=skipBlanks(str);

		r->body_size=0;
		if (allows_empty_body(connective_idx) && *str=='.')
		{	finished=1;
			make_char_available(str,1);
			str++;
		}
		else
			finished=0;
		while(!finished)
		{	
			if (r->body_size>=MAX_BODY)
			{	printf("ERROR: MAX BODY SIZE OF %d EXCEEDED!\n",MAX_BODY);
				exit(1);
			}

			item_ptr_next=recognizeExtLit(str,&a);
			if (item_ptr_next==NULL)
			{	printf("%s: SYNTAX ERROR AT: \'%s\'\n",error_position(str),str);
				return(NULL);
			}

			body[r->body_size]=a;
			r->body_size++;

			str=item_ptr_next;

			str=skipBlanks(str);

			if (*str!=',' && *str!='.')
			{	printf("%s: SYNTAX ERROR: EXPECTED ',' OR '.' AT \'%s\'\n",error_position(str),str);
				exit(1);
			}

			make_char_available(str,1);
			finished=(*str++=='.');
		}

		r->body=calloc(r->body_size,sizeof(struct item *));
		for(i=0;i<r->body_size;i++) r->body[i]=body[i];
	}

	str=skipBlanks(str);

	*ptr_next=str;

#ifdef DEBUG_RULE
	debug_show_rule(r);
#endif

	return(r);
}

void add_domains(char *buff,struct item *atom)
{	int i,j;
	void sprintf_atom(char *buff,struct item *a);

	for(i=0;i<n_rsigs;i++)
	{	if (strcmp(atom->relation,rsigs[i]->relation)==0 &&
		    atom->arity==rsigs[i]->arity)
		{	for(j=0;j<atom->arity;j++)
			{	if (buff[0]!=0) strcat(buff,", ");

				sprintf(&buff[strlen(buff)],"%s(",rsigs[i]->args[j]->relation);

				sprintf_atom(&buff[strlen(buff)],atom->args[j]);

				strcat(buff,")");

				if (atom->args[j]->arity>0) add_domains(buff,atom->args[j]);
			}
		
			return;
		}
	}
}

void add_domains_to_rule(struct rule *r)
{	char domains_buff[MAX_DOMAINS_BUFF];

	int i;

	if (r->type==RULE_SYSTEM_DIRECTIVE) return;	// nothing to be done

	domains_buff[0]=0;
	for(i=0;i<r->head_size;i++)
		add_domains(domains_buff,r->head[i]);

	for(i=0;i<r->body_size;i++)
		add_domains(domains_buff,r->body[i]);

	r->domain_decl=strdup(domains_buff);

#ifdef DEBUG_DOMAIN_DECL
	fprintf(stderr,"DOMAIN DECLARATIONS: \'%s\'\n",r->domain_decl);
#endif
}

void add_domains_to_program(struct node *program)
{	struct node *n;

	for(n=program->next;n!=NULL;n=n->next)
		add_domains_to_rule(n->data);
}

struct rule *get_verbatim(char *str,char **ptr_next)
{	struct rule *r;
	int i;

	/* just store the whole line as a system directive */
	r=calloc(1,sizeof(struct rule));
	r->type=RULE_SYSTEM_DIRECTIVE;
	for(i=0;str[i]!=0 && str[i]!='\n' && str[i]!='\r';make_char_available(str,i+1), i++);	// find EOL
	r->system_directive=calloc(i+1,sizeof(char));
	strncpy(r->system_directive,str,i);

	*ptr_next=&str[i];

	return(r);
}

struct rule *get_directive(char *str,char **ptr_next)
{
	struct item *a;
	char *item_ptr_next;

	int finished;

	str=skipBlanks(str);

/*
	if (*str!='#' ||
	    !(strncmp(&str[1],RSIG_DECL,strlen(RSIG_DECL))==0 &&
	      isspace(str[1+strlen(RSIG_DECL)])))
	{	printf("SYNTAX ERROR! EXPECTED "RSIG_DECL" AT \'%s\'\n",str);
		exit(1);
	}
*/

	make_char_available(str,1+strlen(RSIG_DECL));
	if (!(strncmp(&str[1],RSIG_DECL,strlen(RSIG_DECL))==0 &&
	      isspace((int)str[1+strlen(RSIG_DECL)])))
	{	/* system directive -- just store it */
		struct rule *r;
		int i;

		r=calloc(1,sizeof(struct rule));
		r->type=RULE_SYSTEM_DIRECTIVE;
		for(i=0;str[i]!=0 && str[i]!='\n' && str[i]!='\r';make_char_available(str,i+1), i++);	// find EOL
		r->system_directive=calloc(i+1,sizeof(char));
		strncpy(r->system_directive,str,i);

		*ptr_next=&str[i];

		return(r);
	}

	make_char_available(str,1+strlen(RSIG_DECL));
	str+=1+strlen(RSIG_DECL);

	str=skipBlanks(str);

	finished=0;
	while(!finished)
	{	
		if (n_rsigs>=MAX_RSIGS)
		{	printf("ERROR: MAX RSIGS OF %d EXCEEDED!\n",MAX_RSIGS);
			exit(1);
		}

		item_ptr_next=recognizeAtom(str,&a);
		if (item_ptr_next==NULL) return(NULL);

		rsigs[n_rsigs++]=a;

		str=item_ptr_next;

		str=skipBlanks(str);

		if (*str!=',' && *str!='.')
		{	printf("%s: SYNTAX ERROR: EXPECTED ',' OR '.' AT \'%s\'\n",error_position(str),str);
			exit(1);
		}

		make_char_available(str,1);
		finished=(*str++=='.');
	}

	str=skipBlanks(str);

	*ptr_next=str;

	return(NULL);
}

void sprintf_atom(char *buff,struct item *a)
{	if (a->default_negation) strcat(buff,"not ");
	if (a->strong_negation) strcat(buff,"-");

	if (a->is_infix && a->arity==2)	/* arity==2 should always be the case, but let's check to increase robustness */
	{	sprintf_atom(&buff[strlen(buff)],a->args[0]);

		sprintf(&buff[strlen(buff)]," %s ",a->relation);

		sprintf_atom(&buff[strlen(buff)],a->args[1]);
	}
	else
	{	int i;

		strcat(buff,a->relation);

		if (a->arity>0 && !a->is_parenthesis && !a->skip_parentheses)
			strcat(buff,"(");

		for(i=0;i<a->arity;i++)
		{	if (i>0) strcat(buff,", ");

			/*
			 * [marcy 072909]
			 * lparse does not like extra parentheses. As a workaround,
			 * when outputting the arguments of a relation, we check
			 * each argument to see if it starts with a parenthesis.
			 * If it does, the the parenthesis itself has arity 1,
			 * then we discard the parenthesis and repeat the
			 * check on the parenthesis' argument.
			 */
			struct item *b;
			
			b=a->args[i];
			
			while(b->relation[0]=='(' && b->arity==1)
				b=b->args[0];

			sprintf_atom(&buff[strlen(buff)],b);
		}

		if (a->is_parenthesis)
			sprintf(&buff[strlen(buff)],"%c",a->arglist_end);
		else
		if (a->arity>0 && !a->skip_parentheses)
			strcat(buff,")");
	}
}

void output_atom_to_file(struct item *a,FILE *fp)
{	if (a->default_negation) fprintf(fp,"not ");
	if (a->strong_negation) fprintf(fp,"-");

	if (a->is_infix && a->arity==2)	/* arity==2 should always be the case, but let's check to increase robustness */
	{	int paren_added;

		/* We must make sure the priorities of operators are respected.
		   Rather than implementing a priority table, we just surround
		   all arguments with parentheses.
		   To limit the number of parentheses a little, we skip them
		   if the subtree starts with the same relation as the current
		   node.
		*/
		paren_added=0;
		if (!a->is_parenthesis && !a->skip_parentheses && 
		    a->args[0]->arity>0 && a->args[0]->is_infix &&
		    strcmp(a->args[0]->relation,"(")!=0 &&
		    strcmp(a->args[0]->relation,a->relation)!=0)
		{	fprintf(fp,"(");
			paren_added=1;
		}
		output_atom_to_file(a->args[0],fp);
		if (paren_added)
			fprintf(fp,")");

		/* note that infix relations don't take "not" or "-" */
		fprintf(fp," %s ",a->relation);

		paren_added=0;
		if (!a->is_parenthesis && !a->skip_parentheses && 
		    a->args[1]->arity>0 && a->args[1]->is_infix &&
		    strcmp(a->args[1]->relation,"(")!=0 &&
		    strcmp(a->args[1]->relation,a->relation)!=0)
		{	fprintf(fp,"(");
			paren_added=1;
		}
		output_atom_to_file(a->args[1],fp);
		if (paren_added)
			fprintf(fp,")");
	}
	else
	{	int i;

		fprintf(fp,"%s",a->relation);

		if (a->arity>0 && !a->is_parenthesis && !a->skip_parentheses)
			fprintf(fp,"(");

		for(i=0;i<a->arity;i++)
		{	if (i>0) fprintf(fp,", ");

			/*
			 * [marcy 072909]
			 * lparse does not like extra parentheses. As a workaround,
			 * when outputting the arguments of a relation, we check
			 * each argument to see if it starts with a parenthesis.
			 * If it does, the the parenthesis itself has arity 1,
			 * then we discard the parenthesis and repeat the
			 * check on the parenthesis' argument.
			 */
			struct item *b;
			
			b=a->args[i];
			
			while(b->relation[0]=='(' && b->arity==1)
				b=b->args[0];

			output_atom_to_file(b,fp);
		}

		if (a->is_parenthesis)
			fprintf(fp,"%c",a->arglist_end);
		else
		if (a->arity>0 && !a->skip_parentheses)
			fprintf(fp,")");
	}
}

void output_atom(struct item *a)
{	output_atom_to_file(a,stdout);
}

void output_rule_to_file(struct rule *r,FILE *fp)
{	int i;

	if (r->type==RULE_SYSTEM_DIRECTIVE)
	{	fprintf(fp,"%s\n",r->system_directive);
		return;
	}

	if (r->name!=NULL)
	{	output_atom_to_file(r->name,fp);
		fprintf(fp,": ");
	}

	for(i=0;i<r->head_size;i++)
	{	if (i>0) fprintf(fp," v ");
		output_atom_to_file(r->head[i],fp);
	}

	if (r->body_size>0 || (r->type!=RULE_REGULAR) || (r->domain_decl!=NULL && r->domain_decl[0]!=0))	/* if rule has a non-empty body, or if it is not a regular rule (which replaces ":-." by ".") */
	{	fprintf(fp," %s\n  ",rule_connective(r));

		if (r->domain_decl!=NULL && r->domain_decl[0]!=0)
		{	fprintf(fp,"%s",r->domain_decl);

			if (r->body_size>0)
				fprintf(fp,",\n  ");
		}

		for(i=0;i<r->body_size;i++)
		{	if (i>0) fprintf(fp,", ");

			output_atom_to_file(r->body[i],fp);
		}
	}

	fprintf(fp,".\n\n");
}

void output_rule(struct rule *r)
{	output_rule_to_file(r,stdout);
}

void output_program_to_file(struct node *program,FILE *fp)
{	struct node *n;

	for(n=program->next;n!=NULL;n=n->next)
		output_rule_to_file(n->data,fp);
}

void output_program(struct node *program)
{	output_program_to_file(program,stdout);
}

struct node *parse_program(int n_files,char *files[])
{
#define BEGIN_VERBATIM_BLOCK "#begin_verbatim_block."
#define END_VERBATIM_BLOCK "#end_verbatim_block."
#define VERBATIM "#verbatim "

	struct rule *r;
	struct node *program,*n;

	char *p;
	char str[MAX_STATEMENT_LEN];

	int in_verbatim_block;

	int i;

	program=calloc(1,sizeof(struct node));	/* head of the list */
	n=program;

	buff_start=str;
	to_read=0;
	p=str;
	for(i=0;i<n_files;i++)
	{	if (curr_file!=NULL)
		{	free(curr_file);
			curr_file=NULL;
		}

		if (files==NULL)
		{	reading_fp=stdin;
			curr_file=strdup("<standard input>");
		}
		else
		{	reading_fp=fopen(files[i],"r");
			if (reading_fp==NULL)
			{	printf("Error: unable to open \'%s\'\n",files[i]);
				exit(1);
			}
			curr_file=strdup(files[i]);
		}

		buffer_curr_line=1;

		make_char_available(p,1);

		p=skipBlanks(p);

		in_verbatim_block=0;
		while(*p!=0)
		{	char *ptr_next;
			int i;

			if (in_verbatim_block)
			{	make_char_available(p,strlen(END_VERBATIM_BLOCK));

				if (strncmp(p,END_VERBATIM_BLOCK,strlen(END_VERBATIM_BLOCK))==0)
				{	r=NULL;	/* nothing to store */
					in_verbatim_block=0;
					ptr_next=&p[strlen(END_VERBATIM_BLOCK)];
				}
				else
				{	r=get_verbatim(p,&ptr_next);
					if (ptr_next==NULL) break;
				}
			}
			else
			if (*p=='#')
			{	/* read chars if needed to allow comparisons with keywords */
				make_char_available(p,strlen(VERBATIM));
				make_char_available(p,strlen(BEGIN_VERBATIM_BLOCK));
				if (strncmp(p,BEGIN_VERBATIM_BLOCK,strlen(BEGIN_VERBATIM_BLOCK))==0)
				{	r=NULL;	/* nothing to store */
					in_verbatim_block=1;
					ptr_next=&p[strlen(BEGIN_VERBATIM_BLOCK)];
				}
				else
				if (strncmp(p,VERBATIM,strlen(VERBATIM))==0)
				{	r=get_verbatim(&p[strlen(VERBATIM)],&ptr_next);
					if (ptr_next==NULL) break;
				}
				else
				{	r=get_directive(p,&ptr_next);
					if (ptr_next==NULL) break;
				}
			}
			else
			{	r=get_rule(p,&ptr_next);
				if (r==NULL) break;
			}

			if (r!=NULL)
			{	n->next=calloc(1,sizeof(struct node));

				n=n->next;

				n->data=r;
			}

			if (ptr_next>buff_start)
			{	/* shift the read buffer left:
				 * (1) increase the buffer_curr_line counter by whatever newlines
				 *     are in the part of the buffer that will be lost.
				 */
				for(i=0;&buff_start[i]<ptr_next;i++) if (buff_start[i]=='\n') buffer_curr_line++;
				/* (2) perform the actual shift */
				for(i=0;ptr_next[i]!=0;i++) buff_start[i]=ptr_next[i];
				buff_start[i]=0;
				to_read-=(ptr_next-buff_start);
			}
			p=buff_start;

			if (in_verbatim_block)
				/* if in verbatim block, skip only CR-LFs */
				p=skipCRLFs(p);
			else
				p=skipBlanks(p);
		}

		if (reading_fp!=stdin) fclose(reading_fp);

	}

	return(program);
}

char *parser_version(void)
{	return(PARSER_VERSION);
}
