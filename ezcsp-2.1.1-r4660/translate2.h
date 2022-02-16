#ifndef EZCSP_TRANSLATE_2_H
#define EZCSP_TRANSLATE_2_H

// Copyright (C) 2009-2021 Marcello Balduccini. All Rights Reserved.

#include <string>
#include <vector>

#include <exception>
#include <stdexcept>

#include <aspparser/parser.h>

#include "defs.h"

//using namespace std;

#define HASH_MOD 1000
class hash_item
{
public:
	struct item *i;
	int index;

	hash_item(struct item *_i=NULL,int _index=0)
	{	i=_i;
		index=_index;
	}

	int compute_hash_value(void)
	{	return(hash_item::compute_hash_value(i));
	}

	static int compute_hash_value(const struct item *i)
	{	int h;

		h=0;

		if (i->relation!=NULL)
			for(int j=0;i->relation[j];h=(h+i->relation[j++]) % HASH_MOD);

		for(int j=0;j<i->arity;h=(h+compute_hash_value(i->args[j++])) % HASH_MOD);
		
		return(h);
	}
};

class CSP
{
public:

	std::vector<struct item *> sorted_facts;

	std::string domain;

	std::vector <struct item *> cspvar;
	std::vector <struct item *> required;
	//std::vector <struct item *> label_order;
	std::vector <std::vector <struct hash_item *> > label_order_hash;

	std::vector <struct item *> lpinteger;
	struct item *objective;

	std::vector <std::string> label_options;

	std::vector <struct item *> labeling;
	std::vector <std::vector <struct hash_item *> > labeling_hash;

	CSP()
	{	domain="fd";
		objective=NULL;
	}
};

struct syntax_map
{	char *to, *from;
	int which_solvers;	/* 0->any; bit 0 set -> sicstus4; bit 1 set -> sicstus3; bit 2 set -> bprolog; ... */
	bool infix;
};


int get_var_index(CSP *csp,struct item *var);
std::vector<int> replace_ezcsp_vars(CSP *csp,struct item *v);
void expand_functor(struct item *a);

/* FILES is an array of filenames; each "-" filename is stdin */
int translate2(int cpsolver_type,bool allow_unsupported,bool relaxed_labeling,std::vector<std::string> flist,std::string ofile="-") throw(std::runtime_error);

/* FILE is a filename or "-" for stdin */
int translate2(int cpsolver_type,bool allow_unsupported,bool relaxed_labeling,std::string FILE,std::string ofile="-") throw(std::runtime_error);

#endif /* EZCSP_TRANSLATE_2_H */
