/*
 * File main.cc 
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

//3.53 version Aug 24, 05 removed hend1,pend1,nend1 from the rules
//that used to be copies of hen,pend,nend
//
//3.54 version Aug 25, 05:
//(1) bug at buildingLoopFormulas fixed so it could cause 
//problems for nontight programs
//(2) bug with rules ...v A v...:-..A... not being remove is fixed
//3.55 version Sep 21, 05:
//(1) Zchaff version 2004.11.15 is incorporated in place of Zchaff 2003
//(2) Cmodels is made compatable with gcc3.4/4.* thanks too Wolfgang Faber
//3.57 Includes
//        HCF check        
//        modularity in model checking
//        loopformula by default
//3.58 fixes the bug with loopformula from now on for disj programs only part of loop formula is added where head atom is sat
//    
//3.59 includes -eloop flag that performs elementary set computation
// and adds loop formulas of elementary loops when needed
// 
//3.60 tightness bug fix through away SCC of 1 element
//     now all the unsat loops are added 
//
//3.6x    Ilkka's circuit component's 
//        where implemented -bc flag is used plus bcircuit program
//        must be present  
//        impl is preliminary hence output is not readable
//        no positive time results were gained
//        as Cmodels CNF representation is more compact and seem to 
//        be better suit
//3.63 Datastructures added to support linear time WFM, and Reduct
//
//3.64-65 Bug fixes at WFM
//
//3.66 Bug fixes Zchaff to be portable into 64 bit archetecture
// Thanks to Yinlei Yu: 
// zchaff_dbase.cpp, line 324. Replacing "int displacement" with
//"long long displacement"
//3.67 Bug fixes Zchaff to be portable into 64 bit archetecture
// Thanks to Andre Neumann: on 64 bit archetecture UNSAT when SAT, due to no 
// return true; in the end of createClauses 
// zchaff_dbase.cpp, line 324. Replacing "int displacement" with
//"long long displacement"
// 
// 3.68 Esra's bug fix that could occur on constraint rules translation
// where new_atom was created instead of a false atom 
// + improved simplification
// + Added flag -ms that allows calling MINISAT
//    Minisat is now incorporated into Cmodels,
//    its code has been added as part of Cmodels
//    two functions added to SimpSolver to allow
//    adding clauses from cmodels, and getting feedback from a solver
//    once solution is found
//    Minisat and Zchaff communication is alike 
// + bug fixes for choice rules as {k}:-k.
// + bug fix with Weights that were not allowed to drop below negative value 
// version 3.69 
// + replaced zChaff version from 2004 with zChaff 2007.3.12
// + added check on what addClause from Minisat returns, since when
//   it returns false the instance is UNSAT.
// + -zca flag added only for comparison reasons of incremental SAT solving and 
//   assat method
// cmodels 3.70
// Esra's bug Fix
// WFM bug
//void ConstraintRule::HeadInOneRule(Atom* at)
//void     WeightRule::HeadInOneRule(Atom* at){
//some of the atoms could have been assigned values by now
//for instance a:-1{falseassigned1, notassigned}
//in such case only notassigned should be assigned computetrue
//Such bug could not appear in Basic, choice or disj rules
//
//
//3.71 improvement of clausification by not inroducing aux atom
//when -a occurs in the body i.e, avoiding intoruding clauses for aux_1==-a 
//+fixing intro two aux atoms for the same room
//
//3.73 atmost is computed (wfs--complete); sorting is introduced to disregard
//  same bodies in rules, and also the rules that are subsummed by others
//
//3.74 bug fixes due to Benjamin Kaufmann
// (i) weightrule Atmost computation
// (ii) completionchoice 
// (iii) weight rule elimination inefficiency in translation is removed 
//      (compare worked unproperly) cmodels worked correctly but inefficiently
//3.75 bug fix due to  Christian Drescher drescher@cs.uni-potsdam.de
//(occured in 3.73 not previously and only for the case of 
//disjunctive programs i.e.
// a v b:-c would be represented as two clauses: -c v a; -c v b 
// in place of -c v a v b
//
//+ following Benjamin suggestion changed minisatSolver->solve(true,false))
//  to minisatSolver->solve(true,true)) that disables farther than first time
//  preprocessing in minisat
//
//3.76 bug fixed in loop formula construction due to not cleanscc
//3.77 bug fixed in loop formula construction due to not cleanscc
//
//Minisat version 1 is added -ms1
//-loopformula1 flag (just one loopformula at a time is added
// instead of all
//-temp flag in case of Minisat v 1(-ms1) learns and forgets loop formulas
//
//
//3.78 bug fixed in read.cc 
//int Read::addWeightRule (FILE *f) 
// now reading is done with add_head() 
// in place of add_head_repetition 
// bug was reported by Roland Kaminski 26 Feb Fri 
//(it could occur only on programs with weight rules)
//3.79 
// 1) bug fixed in cmodels.cc 
// bool Cmodels::rec_weight_rule(Weight totalweight, int sizeC, Atom* headC,
//		     unsigned long atleast, int counter_body)
//
//weightrules translation had a bug by assigning the same atom to 
//two different expressions (see comments in the code that specify what was changed)
//
// bug was reported by  Raphael Finkel  10 Mar 2009
//(it could occur only on programs with weight rules)
// 2) in zchaff_dbase.cc displacement given a new type
//    to support both 32 and 64 bit archetectures in uniform manner.
//    The change is suggested by  Gurucharan Huchachar 11 Mar 2009
//    Line 329 zchaff_dbase.cc :
//    ptrdiff_t displacement = _lit_pool_start - old_start;
//    For 64 bit archetecture
//3.80
// minisat is now default instead of zchaff
//
//3.81
// capability for incremental ASP is added; please see ctable.h file 
// that contains all the details of the interface
//3.82
// under construction
// idea to implement an additional propagation of minisat 1 on cmodels side 
// so that non-lazy approach were possible with EZ-CSP or other system if it needs to
// 3.82g -> h bug fix due to Benjamin Kaufmann clearLoop added at cmodels.cc 4847
// 3.83 per Marcello's request change in partial assignment return to external solver. Now it is more flexible which atoms external solver wants to see. See ctable.h for Docs.
// 3.84 bug fix reported by Peter Schueller. Occurred in addDenial cmodels.cc
// 3.86 introduced -cdimacs flag to allow ezsmt 
//      to use cmodles capability compute completion
// 3.86.1 fixed declarations in Minisat so that gcc compiler version 5+ compiles the code (due to Marcello Balduccini)  
//      introduced -file option to pass filename as a parameter for reading (due to Ben Susman) 

#include <iostream>
#include <new>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include "ctable.h"
#include "timer.h"
#include "interpret.h"
#include <time.h>
#include <sstream>
#include <ctype.h>
#include <fstream>

using namespace std;

Ctable ctable;
bool Atom::change = false;
bool Atom::conflict = false;
void a_new_handler ()
{
  cerr << "operator new failed: out of memory" << endl;
  exit(23);
}
static void timeOutHandler(int sig)
{
  switch (sig) {

#ifndef _WIN32	// marcy
  case SIGXCPU:
#ifndef SHORT_OUT
    ctable.cmodels.output.PrintStats();
#else
    ctable.cmodels.output.PrintStats();
#endif
    break;
#endif
  default:
    fprintf(stderr, "Unknown event\n");
    break;
  }

  exit (22);
}


int main (int argc, char *argv[])
{


  Timer mainTimer;
  

  set_new_handler (&a_new_handler);
  bool error = false;
 



  strcpy(ctable.cmodels.param.cmodelsname, &argv[0][0]);

  strcpy(ctable.cmodels.param.config, "CONFIG");
  
  for (int c = 1; c < argc && !error; c++){
    if (c+1<argc){
      c=c+ctable.setSingleExecutionArgument(&argv[c][0],&argv[c+1][0]);
    }
    else
      c=c+ctable.setSingleExecutionArgument(&argv[c][0],NULL);
  }


  //if the timeout was set then we will set the function for timeout
  if(ctable.cmodels.param.timeout!=0)    
     mainTimer.SetTimeout(ctable.cmodels.param.timeout, timeOutHandler);


  //This is not possble at the moment unless we include
  //clausification of loop formulas using many clauses
  //  if(ctable.cmodels.sys == 3 & ctable.cmodels.le)
    //    ctable.cmodels.sys =6; //here we force zchaff 
  //with incremental learning to be our choice of a sat solver
  
	
  //we find the path to cmodels and assume that config file is located there
  if(strcmp(ctable.cmodels.param.config,"\0")==0){
    char path_to_config[100];
    int k=0; 
    path_to_config[k]='\0';
    int length = strlen(ctable.cmodels.param.cmodelsname);
    int l = length-1;
    while(l!=-1 && ctable.cmodels.param.cmodelsname[l]!='/'){
      l--;
    }
    if(l>=0){
      for( k= 0;k<=l;k++)
	path_to_config[k]= ctable.cmodels.param.cmodelsname[k];
      path_to_config[k]='\0';
    }
    strcat(path_to_config, "CONFIG");
    strcpy(ctable.cmodels.param.config, path_to_config);
  }
 
  if (error)
    {
      ctable.usage ();
      return 1;
    }
  if(ctable.cmodels.output.asparagus==STANDARD)
    cerr << "ezsmt version 2.0.0 (ezsmtPlus) Reading..."<<endl;;


  if(ctable.cmodels.param.numOfFiles==0){
	  ctable.usage ();
  	  exit(1);
  }

  //preparsing
  stringstream ss;
  ss.clear();
  ss.str("");
  ss << "$EZSMTPLUS/ezcsp-2.1.1-r4660/pre-parser ";
  for( int a = 0; a< ctable.cmodels.param.numOfFiles ; a++){
	  if ( access( ctable.cmodels.param.files[a], F_OK ) == -1 ){
		  cerr <<" *** Error: file "<<ctable.cmodels.param.files[a]<<" does not exist. ***"<<endl;
		  exit(1);
	  }

	  ss<<ctable.cmodels.param.files[a]<<" ";
  }
  ss<<" > "<<ctable.cmodels.param.file<<".preparsed";

  cerr<<endl<<"Running pre-parsing command: "<<ss.str().c_str()<<endl;;
  system(ss.str().c_str());

  //Check errors from preparsing output
  ostringstream outputFile;
  ss.clear();
  ss.str("");
  ss<<ctable.cmodels.param.file<<".preparsed";
  ifstream in_file(ss.str().c_str());
  outputFile <<in_file.rdbuf();
  string outputFilelStr= outputFile.str();
  in_file.close();
  istringstream iss(outputFilelStr);
  string line;
  while(getline(iss,line)){
  //if a error is read, output error message
    	if(line.find("SYNTAX ERROR")!=string::npos){
    	     cout << " *** Error during preparsing. See output file " <<ctable.cmodels.param.file<<".preparsed ***"<< endl;
    	     exit(1);
    	}
  }


  //grounding
  ss.clear();
  ss.str("");
  ss<<"$EZSMTPLUS/tools/gringo "<<ctable.cmodels.param.file<<".preparsed"<<" > "<<ctable.cmodels.param.file<<".grounded";
  cerr<<"Running grounding command: "<<ss.str().c_str()<<endl;;
  system(ss.str().c_str());


  //Check errors from grounding output
   ostringstream outputFile2;
   ss.clear();
   ss.str("");
   ss<<ctable.cmodels.param.file<<".grounded";
   ifstream in_file2(ss.str().c_str());
   outputFile2 <<in_file2.rdbuf();
   string outputFilelStr2= outputFile2.str();
   in_file2.close();
   istringstream iss2(outputFilelStr);
   while(getline(iss2,line)){
   //if a error is read, output error message
     	if(line.find("error: ")!=string::npos  || line.find("ERROR: (gringo): ")!=string::npos){
   	     cout << " *** Error during grounding. See output file " <<ctable.cmodels.param.file<<".grounded ***"<< endl;
   	     exit(1);
       }
   }


  strcat(ctable.cmodels.param.file, ".grounded");

  ctable.cmodels.output.timerAll.start();

  if(strlen(ctable.cmodels.param.file) > 0)
  {
      freopen(ctable.cmodels.param.file,"r",stdin);
  }

  int bad = ctable.read(stdin);  
  if(ctable.cmodels.output.asparagus==STANDARD)
	cerr << "done"<<endl;       
  if (bad)
    {
      cerr << "Error in input" << endl;
      return 1;
    }
  //removes some setting that might be not fitting
  //for some specific SAT solver
  ctable.cmodels.param.finish();

   ctable.calculate();
   /*	 

   //	  for DEBUGGING externals replace above line with the following comented code
  ctable.setSolver(MINISAT1);
  int numLits=ctable.getNumberGroundedAtoms();
  int* answerset_lits = new int[numLits];
  ctable.Initialize(answerset_lits, numLits);
  if (numLits!=-2){
	cerr<<"preporcessing is sufficient here";
	exit(23);
  }
  answerset_lits[0]=2;
  answerset_lits[1]=3;
  //  answerset_lits[2]=4;
  //answerset_lits[3]=5;
  //answerset_lits[4]=6;
  numLits=2;
  ctable.markExternallyConstrainedAtoms (answerset_lits, numLits);

  numLits=ctable.getNumberGroundedAtoms();
  bool* assignments= new bool [ctable.cmodels.program.number_of_atoms];
  ctable.Solve(answerset_lits, numLits);

  int inner_count=0;
	//by default assignment and constraint_lits is false

	for(int j=0; j<ctable.cmodels.program.cmodelsAtomsFromThisId; j++){
	  assignments[j]= false;
	}

	for (int i=0; i<numLits; i++){
	  for(int indA=inner_count; indA<ctable.cmodels.program.cmodelsAtomsFromThisId; indA++){
		inner_count++;
		if(answerset_lits[i]==ctable.cmodels.program.atoms[indA]->get_lparse_id()){
		  
		  assignments[indA]= true;		  

		  break;
		}
	  }
	}  
	for (long i=0;i<ctable.cmodels.program.cmodelsAtomsFromThisId;i++){
	  if(assignments[i]){
		if(strcmp("#noname#",	ctable.cmodels.program.atoms[i]->atom_name()))
			printf("%s ",	ctable.cmodels.program.atoms[i]->atom_name ());
		  
	   
      }
    }  
   */
  ctable.cmodels.output.timerAll.stop();
  ctable.cmodels.output.print();

  return 0;
}

