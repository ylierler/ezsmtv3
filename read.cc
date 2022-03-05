/*
 * File read.cc 
 * Last modified on 2 19:34 2002
 * By Yuliya Babovich 
 *
 */

// Copyright 1998 by Patrik Simons
// This program is free software; you can redistribute it and/or
// modify it under the terms of the GNU General Public License
// as published by the Free Software Foundation; either version 2
// of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place - Suite 330, Boston,
// MA 02111-1307, USA.
//
// Patrik.Simons@hut.fi
#include <cstdlib>
#include <exception>
#include <fstream>
#include <iostream>
#include <float.h>
#include <limits.h>
#include <sstream>
#include <stdexcept>
#include <string.h>
#include "atomrule.h"
#include "program.h"
#include "read.h"

Read::Read (Program *p, Api *a)
  : program (p), api (a)
{
  // atoms = 0;
  size = 0;
  models = 1;
}

//distractor
//
Read::~Read ()
{
  delete[] atoms;
}

//
//in case if array of atoms is not big enough already it will grow
//
void
Read::grow ()
{
  long sz = size*2;
  if (sz == 0)
    sz = 256;
  Atom **array = new Atom *[sz];
  long i;
  for (i = 0; i < size; i++)
    array[i] = atoms[i];
  size = sz;
  for (; i < size; i++)
    array[i] = 0;
  delete[] atoms;
  atoms = array;
}

//
//creates an instance of a new atom
//
// FIXME Why do we use Atoms here? This seems like a leak of domain boundaries
Atom *
Read::getAtom (long n)
{
  while (n >= size)
    grow ();
  if (atoms[n] == 0)
    atoms[n] = api->new_atom (n);
  return atoms[n];
}

Atom* Read::getAtomFromLiteral(long n)
{
  return getAtom(abs(n));
}

Atom *
Read::getFalseAtom (long n)
{
  while (n >= size)
    grow ();
  if (atoms[n] == 0)
    atoms[n] = api->new_atom (n);
  if(n==1 && strcmp("#noname#",atoms[n]->atom_name ())==0){
	//    atoms[n]->Bneg=true;
	//   api->set_name (atoms[n], 0);   
    program->false_atom=atoms[n];
  }
  return atoms[n];
}

int
Read::finishReading(FILE* f, long size){
  long n;
  int count;

  for (long i = 0; i < size; i++)
    {
	  count = fscanf(f,"%ld",&n);	  
      if (count == EOF || n < 1)
		{
		  cerr << "atom out of bounds, line " << linenumber << endl;
		  return 1;
		}
	}
  return 0;
}

// gringo's output used to separate positive and negative portions of the body
int
Read::readBody (FILE *f, long size, bool pos, RuleType type)
{
  long n;
  int count;
  for (long i = 0; i < size; i++)
    {
	  count = fscanf(f,"%ld",&n);	  
    //   if (count == EOF || n < 1)
		// {
		//   cerr << "atom out of bounds, line " << linenumber << endl;
		//   return 1;
		// }
      Atom *a = getAtom (n);
      // if(!pos)
      //   a->scopeNegAsFail = true;

	  //if atom is not added 
	  //it meens that it is repeated again in the rule
	  //and since it is a weight rule we might loose information
	  if(type==WEIGHTRULE||type==CONSTRAINTRULE){
      a->pbInd.clear();
      a->nbInd.clear();
      api->add_body (a, pos);
	  }
	  else
		if(!api->add_body_repetition (a, pos, type)){		  
		  for (i=i+1; i < size; i++)
			{
			  count = fscanf(f,"%ld",&n);
			  // if (count == EOF || n < 1)
				// {
				//   cerr << "atom out of bounds, line " << linenumber << endl;
				//   return 1;
				// }
			}
      // TODO revisit
		  api->rule_reset_repetition();
		  return -1; //there is no point going this rule father
		  // as we can thru this rule away due to same atom in
		  // head and pbody for instance or same atom in pos and neg part of the body
		}
    }
  return 0;
}

int
Read::addBasicRule (FILE *f)
{
  long n;
  int count;
  //  cout<<"BASICRULE"<<endl;
  api->begin_rule (BASICRULE);
  // Rule head
  count = fscanf(f,"%ld",&n);
  // if (count == EOF || n < 1)
  //   {
  //     cerr << "head atom out of bounds, line " << linenumber << endl;
  //     return 1;
  //   }
  Atom *a = getAtom (n);
  api->add_head_repetition (a);
  // Body
  count = fscanf(f,"%ld",&n);
  // if (count == EOF || n < 0)
  //   {
  //     cerr << "total body size, line " << linenumber << endl;
  //     return 1;
  //   }
  long body = n;
  // Negative body
  count = fscanf(f,"%ld",&n);

  // if (count == EOF || n < 0 || n > body)
  //   {
	//   cout<<n<<endl;
	//   cout<<body<<endl;
  //     cerr << "negative body size, line " << linenumber << endl;
  //     return 1;
  //   }
  //  cout<<" Reading Negative part "<<endl;
  int retRB=readBody (f, n, false,BASICRULE);
  switch (retRB){
  case 0:
	break;
  case -1:
	return finishReading(f, body-n);
  case 1:
	return 1;

  }
  //  cout<<" Reading Positive part "<<endl;
  // Positive body
  retRB=readBody (f, body-n, true,BASICRULE);
  switch (retRB){
  case 0:
	api->end_rule ();

	return 0;
  case -1:
	return 0;
  case 1:

	return 1;

  }

 
}

int
Read::addConstraintRule (FILE *f)
{
  long n;
  int count;
  api->begin_rule (CONSTRAINTRULE);
  // Rule head
  count = fscanf(f,"%ld",&n);
  if (count == EOF)
    return 1;
  if (count == EOF || n < 1)
    {
      cerr << "head atom out of bounds, line " << linenumber << endl;
      return 1;
    }
  Atom *a = getAtom (n);
  api->add_head(a);
  // Body
  count = fscanf(f,"%ld",&n);
  if (count == EOF || n < 0)
    return 1;
  long body = n;
  // Negative body
  count = fscanf(f,"%ld",&n);
  if (count == EOF || n < 0 || n > body)
    return 1;
  long nbody = n;
  // Choose
  count = fscanf(f,"%ld",&n);
  if (count == EOF || n < 0 || n > body)
    return 1;
  api->set_atleast_body (n);
  if (readBody (f, nbody, false,CONSTRAINTRULE)==1)
    return 1;
  // Positive body
  if (readBody (f, body-nbody, true,CONSTRAINTRULE)==1)
    return 1;
  api->end_rule ();
  return 0;
}

int
Read::addGenerateRule (FILE *f)
{
  fclose(f);
  cerr << "generate rules are not interpreted by cmodels, line " 
	   << linenumber << endl;
  return 1;

}


int
Read::addChoiceRule (FILE *f)
{
  long n;
  int count;
  api->begin_rule (CHOICERULE);
  // Heads
  count = fscanf(f,"%ld",&n);
  if (count == EOF || n < 1)
    {
      cerr << "head size less that one, line " << linenumber << endl;
      return 1;
    }
  long heads = n;
  for (long i = 0; i < heads; i++)
    {
	  count = fscanf(f,"%ld",&n);
      if (count == EOF || n < 1)
	{
	  cerr << "atom out of bounds, line " << linenumber << endl;
	  return 1;
	}
      Atom *a = getAtom (n);
      api->add_head_repetition (a);
    }
  // Body
  count = fscanf(f,"%ld",&n);
  if (count == EOF || n < 0)
    {
      cerr << "total body size, line " << linenumber << endl;
      return 1;
    }
  long body = n;
  // Negative body
  count = fscanf(f,"%ld",&n);
  if (count == EOF || n < 0 || n > body)
    {
      cerr << "negative body size, line " << linenumber << endl;
      return 1;
    }
  int retRB=readBody (f, n, false,CHOICERULE);
  switch (retRB){
  case 0:
	break;
  case -1:
	return finishReading(f, body-n);
  case 1:
	return 1;

  }
  // Positive body
  retRB=readBody (f,body-n, true,CHOICERULE);
  switch (retRB){
  case 0:
	api->end_rule ();
	return 0;
  case -1:
	return 0;
  case 1:
	return 1;

  }


}
int
Read::addDisjunctionRule (FILE *f)
{
  long n;
  int count;
  api->begin_rule (DISJUNCTIONRULE);
  // Heads
  count = fscanf(f,"%ld",&n);
  if (count == EOF || n < 1)
    {
      cerr << "head size less than one, line " << linenumber << endl;
      return 1;
    }
  long heads = n;
  for (long i = 0; i < heads; i++)
    {
	  count = fscanf(f,"%ld",&n);
      if (count == EOF || n < 1)
	{
	  cerr << "atom out of bounds, line " << linenumber << endl;
	  return 1;
	}
      Atom *a = getAtom (n);
      api->add_head_repetition (a);
    }
  // Body
  count = fscanf(f,"%ld",&n);
  if (count == EOF || n < 0)
    {
      cerr << "total body size, line " << linenumber << endl;
      return 1;
    }
  long body = n;
  // Negative body
  count = fscanf(f,"%ld",&n);
  if (count == EOF || n < 0 || n > body)
    {
      cerr << "negative body size, line " << linenumber << endl;
      return 1;
    }
  int retRB=readBody (f, n, false,DISJUNCTIONRULE);
  switch (retRB){
  case 0:
	break;
  case -1:
	return finishReading(f, body-n);
  case 1:
	return 1;

  }
  // Positive body
  retRB=readBody (f, body-n, true,DISJUNCTIONRULE);
  switch (retRB){
  case 0:
	api->end_rule ();
	return 0;
  case -1:
	return 0;
  case 1:
	return 1;

  }


}

int
Read::addWeightRule (FILE *f)
{
  long n;
  int count;
  // Rule head
 
  api->begin_rule (WEIGHTRULE);
  // Rule head
  count = fscanf(f,"%ld",&n);
  if (count == EOF || n < 1)
   {
      cerr << "head atom out of bounds, line " << linenumber << endl;
      return 1;
    }
  Atom *a = getAtom (n);
  api->add_head (a);
  Weight w;
# ifdef USEDOUBLE
  count = fscanf(f,"%DBL_DIGf",&w);
#else
  count = fscanf(f,"%ld",&w);
# endif

  // Atleast
  // count = fscanf(f,"%DBL_DIGf",&w);
  //f >> w;
  if (count == EOF)
    return 1;
  api->set_atleast_weight (w);
  // Body 
  count = fscanf(f,"%ld",&n);
  if (count == EOF || n < 0)
    {
      cerr << "Weight rule, total body size, line " << linenumber << endl;
      return 1;
    }  
  long body = n;
  // Negative body 
  count = fscanf(f,"%ld",&n);

  if (count == EOF || n < 0 || n > body)
    {
      cerr << "Weight rule, negative body size, line " << linenumber << endl;
      return 1;
    }
  long nbody = n;
  if (readBody (f, nbody, false,WEIGHTRULE))
    return 1;
  // Positive body
  if (readBody (f, body-nbody, true,WEIGHTRULE))
    return 1;
  Weight sum = 0;
  for (long i = 0; i < body; i++)
    {
	  # ifdef USEDOUBLE
	  count = fscanf(f,"%DBL_DIGf",&w);
      #else
	  count = fscanf(f,"%ld",&w);
      # endif

      if (count == EOF)
		return 1;
      if (sum+w < sum)
		{
		  cerr << "sum of weights in weight rule too large,"
			   << " line " << linenumber << endl;
		  return 1;
		}
      sum += w;
      if (i < nbody){
		
		api->change_body (i, false, w);
	  }
      else{
		api->change_body (i-nbody, true, w);
	  }
    }
  api->end_rule ();
  return 0;

}

int
Read::addOptimizeRule (FILE *f)
{
  fclose(f);
  cerr << "Optimize rule are not processed by cmodels, line"
	   << linenumber << endl;
  return 1;
 
}


enum StatementType
{
END = 0,
RULE = 1,
MINIMIZE = 2,
PROJECT = 3,
OUTPUT = 4,
EXTERNAL = 5,
ASSUMPTION = 6,
HEURISTIC = 7,
EDGE = 8,
THEORY = 9,
COMMENT = 10
};

enum HeadType
{
DISJUNCTION = 0,
CHOICE = 1
};

enum BodyType
{
NORMAL_BODY = 0,
WEIGHT_BODY = 1
};

// enum HeadType

void Read::readRuleLine(istringstream& line)
{
  // cout << "Reading: " << line << endl;

  // RuleBuilder builder();
  api->begin_rule(BASICRULE);

  int headType, headLength;
  line >> headType >> headLength;

  if (headType == DISJUNCTION)
  {
    for (int i = 0; i < headLength; i++)
    {
      long literal;
      line >> literal;

      Atom* a = getAtomFromLiteral(literal);
      // builder.addHead(literal);
      // api->add_head(getAtom(literal));
      api->add_head_repetition(a);

    }
  }
  else if (headType == CHOICE)
  {
    throw std::runtime_error("Not implemented yet");
  }

  int bodyType, bodyLength;
  line >> bodyType >> bodyLength;

  if (bodyType == NORMAL_BODY)
  {
    for (int i = 0; i < bodyLength; i++)
    {
      long literal;
      line >> literal;

      Atom* a = getAtomFromLiteral(literal);

      // builder.addBody(literal);
      // api->add_body(getAtom(std::abs(literal)), literal > 0);
      api->add_body_repetition(a, literal > 0, BASICRULE);
    }
  }
  else
  {
    throw std::runtime_error("Not implemented yet");
  }

  api->end_rule();
}

void Read::readOutputLine(istringstream& line)
{
  int _;
  int fixme; // FIXME I'm not sure what 1 and 0 represent
  string atomName;
  long atomId;
  line >> _ >> atomName >> fixme >> atomId;

  if (fixme == 1)
  {
    Atom* a = getAtom(atomId);
    api->set_name(a, atomName.c_str());
  }
}

int Read::read(string fileName)
{
  ifstream fileStream(fileName);

  // TODO Error handling
  string line;
  while (std::getline(fileStream, line))
  {
    unique_ptr<istringstream> lineStream(new istringstream(line));

    int statementType;
    *lineStream >> statementType;

    switch (statementType)
    {
      case END:
        break;
      case RULE:
        readRuleLine(*lineStream);
        break;
      case OUTPUT:
        readOutputLine(*lineStream);
        break;
      default:
        // TODO error
        break;
    }
  }

  return 0;

  // Read rules.
  // int type;
  // bool stop = false;
  // for (linenumber = 1; !stop; linenumber++) {


	// // Rule Type
	// fscanf(f,"%d",&type);
	// switch (type)
	//   {
	//   case BASICRULE:
	// 	if (addBasicRule (f))
	// 	  return 1;
	// 	break;
	//   case CONSTRAINTRULE:
	// 	if (addConstraintRule (f))
	// 	  return 1;
	// 	break;
	//   case CHOICERULE:
	// 	if (program->disjProgramLparse){
	// 	  if (addDisjunctionRule (f))
	// 		return 1;
	// 	}else{

	// 	  if (addChoiceRule (f))
	// 		return 1;
	// 	}
	// 	break;
	//   case DISJUNCTIONRULE:
	// 	if (addDisjunctionRule (f)){
	// 	  program->disj=true;
	// 	  return 1;
	// 	}
	// 	break;
	//   case GENERATERULE:
	// 	if (addGenerateRule (f))
	// 	  return 1;
	// 	break;
	//   case WEIGHTRULE:
	// 	if (addWeightRule (f))
	// 	  return 1;
	// 	break;
	//   case OPTIMIZERULE:
	// 	if (addOptimizeRule (f))
	// 	  return 1;
	// 	break;
	//   default:
	// 	cout<< "Default "<<type<< endl;
	// 	cout<< "Line number "<< linenumber<<endl;
	// 	return 1;
	//   }
  // }

  // Read atom names.
  // const int len = 1024;
  // char s[len]; char *ret;
  // long i;
  // int count;
  // //f.getline (s, len);  // Get newline
  // ret = fgets(s,len,f);

  // if (ret == NULL)
  //   {
  //     cerr << "expected atom names to begin on new line, line "
	// << linenumber << endl;
  //     return 1;
  //   }

  // count = fscanf(f,"%ld",&i);

  // ret = fgets(s,len,f);
  // s[strlen(s)-1] = 0;
  // linenumber++;
  // while (i)
  //   {
  //     if (ret == NULL)
	// {
	//   cerr << "atom name too long or end of file, line "
	//        << linenumber << endl;
	//   return 1;
	// }
  //     Atom *a = getAtom (i);
  //     if (*s)
	// api->set_name (a, s+1);
  //     else
	// api->set_name (a, 0);
  //     count = fscanf(f,"%ld",&i);

  //     ret = fgets(s,len,f);
  //     s[strlen(s)-1] = 0;
  //     linenumber++;
  //   }
  // // Read compute-statement
  // ret = fgets(s,len,f);
  // s[strlen(s)-1] = 0;
  // if (ret == NULL || strcmp (s, "B+"))
  //   {
  //     cerr << "B+ expected, line " << linenumber << endl;
  //     return 1;
  //   }
  // linenumber++;
  // count = fscanf(f,"%ld",&i);
  // linenumber++;
  // while (i)
  //   {
  //     if (count == EOF || i < 1)
	// {
	//   cerr << "B+ atom out of bounds, line " << linenumber << endl;
	//   return 1;
	// }
  //     Atom *a = getAtom (i);
  //     api->set_compute (a, true,true);
  //     //api->add_clause_from_compute (a, true);
	//   count = fscanf(f,"%ld",&i);
  //     linenumber++;
  //   }
  // ret = fgets(s,len,f);
  // ret = fgets(s,len,f);
  // s[strlen(s)-1] = 0;
  // if (ret == NULL || strcmp (s, "B-"))
  //   {
  //     cerr << "B- expected, line " << linenumber << endl;
  //     return 1;
  //   }
  // linenumber++;
  // count = fscanf(f,"%ld",&i);
  // linenumber++;
  // while (i)
  //   {
  //     if (count == EOF || i < 1)
	// {
	//   cerr << "B- atom out of bounds, line " << linenumber << endl;
	//   return 1;
	// }
  //     Atom *a = getFalseAtom (i);
  //     api->set_compute (a, false,true);
  //     //api->add_clause_from_compute (a, false);
  //     count = fscanf(f,"%ld",&i);
  //     linenumber++;
  //   }
  // //f >> models;  // zero means all
  // count = fscanf(f,"%ld",&models);
  // if (count == EOF)
  //   {
  //     cerr << "number of models expected, line " << linenumber << endl;
  //     return 1;
  //   }
  // return 0;
}
;
