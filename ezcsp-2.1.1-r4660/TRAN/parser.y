%include {   
#include <iostream>  
#include <stdlib.h>
#include <assert.h>
#include <string.h>
#include <aspparser/parser.h>
#include "parser.h"
#include <stdlib.h>
#include "lexglobal.h"



void copy_item(struct item *src,struct item *dest)
{
	memcpy(dest,src,sizeof(struct item));
}

struct item *dup_item(struct item *i)
{	struct item *dup;

	dup=(struct item *)calloc(1,sizeof(struct item));
	copy_item(i,dup);
	
	return(dup);
}

struct xnode: public node
{	//struct node n;
public:
	struct node *last;
};

static struct node *program=NULL;

}  


%token_type {item*}
%default_type {item*}

%type term {item*}
%type termlist {item*}
%type fact {item*}
%type aset {node*}


%parse_accept
{	
}

   
%syntax_error
{
	std::cout << "Syntax error" << std::endl;  
	exit(1);
}

/*  This is to terminate with a new line */
main ::= aset(A).
	{	
		program=A;
	}
aset(A) ::= .
	{	struct xnode *xA;
		xA=(struct xnode *)calloc(1,sizeof(struct xnode));	/* empty head */
		xA->last=xA;
		A=xA;
	}
aset(A) ::= aset(B) fact(C) PERIOD.
	{	struct rule *r;
		struct xnode *n,*l;

/*
std::cout << "Fact.relation=" << C->relation << std::endl; 
std::cout << "arity=" << C->arity << std::endl;
for(int i=0;i<C->arity;i++)
{	std::cout << "rel" << (i+1) << "=" << C->args[i]->relation << std::endl;
}
std::cout << "infix=" << C->is_infix << std::endl;
*/
		r=(struct rule *)calloc(1,sizeof(struct rule));
		r->head_size=1;
		r->head=(struct item **)calloc(1,sizeof(struct item *));
		r->head[0]=dup_item(C);
		n=(struct xnode *)calloc(1,sizeof(struct xnode));
		n->data=r;
		l=(struct xnode *)((struct xnode *)B)->last;
		//l=B;
		//for(l=B;l->next;l=l->next);
		l->next=n;
		((struct xnode *)B)->last=n;
		A=B;
	}



fact(A) ::= term(B).
	{
		A=B;
		A->is_term=IS_ATOM;
	}  

fact(A) ::= MINUS term(B).
	{	A=B;
		A->strong_negation=1;
		A->is_term=IS_ATOM;
	}  

term(A) ::= NUM(B).
	{	A=B;
		A->is_term=IS_TERM;
	}

term(A) ::= ID(B).
	{	A=B;
		A->is_term=IS_TERM;
	}

term(A) ::= ID(B) LPAREN termlist(C) RPAREN.
	{
		A=C;
		A->relation=B->relation;
		A->is_term=IS_TERM;
	}




termlist(A) ::= term(B).
	{	
		A=(struct item *)calloc(1,sizeof(struct item));
		A->relation=strdup("(");
		A->arity=1;
		A->args=(struct item **)calloc(1,sizeof(struct item *));
		A->args[0]=dup_item(B);
		A->is_term=IS_TERM;
	}

termlist(A) ::= termlist(B) COMMA term(C).
	{	struct item **p;

		//copy_item(&B,&A);
		A=B;//dup_item(B);
		
		p=(struct item **)calloc(A->arity+1,sizeof(struct item *));
		for(int i=0;i<A->arity;i++)
			p[i]=A->args[i];
		p[A->arity]=dup_item(C);
		A->arity++;
		A->args=p;
		A->is_term=IS_TERM;
	}
