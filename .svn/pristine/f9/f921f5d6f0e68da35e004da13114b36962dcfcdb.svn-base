/*
 * File ctable.cc 
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
#include <iostream>
#include <iomanip>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#if defined _BSD_SOURCE || defined _SVID_SOURCE
#include <sys/time.h>
#include <sys/resource.h>
#endif
#include "ctable.h"
#include "time.h" 
 
Ctable::Ctable ()
  : api (&cmodels.program),
    reader (&cmodels.program, &api)
{
  cmodels.api=&api;
  
}

Ctable::~Ctable ()
{
}

int
Ctable::read (FILE *f)
{ 
  
  int r = reader.read (f);
  //the program has just been read; no modifications on the program were performed 
  //so we can safely set the value of program.original_number_of_atoms
  cmodels.program.original_number_of_atoms=cmodels.program.number_of_atoms;
  return r;
}
void 
Ctable::setSolver(SolverType st){  
  cmodels.param.sys=st;
  //this function is assumed to be used only for incremental solving and 
  //Minisat and ZChaff and Minisat1 are the only solvers that will support this
  if (st!=MINISAT&&st!=ZCHAFF&&st!=MINISAT1)
	  cmodels.param.sys=MINISAT1;

}
void 
Ctable::setExecutionArgs(char args[]){  
  char str[256];
  strcpy(str,args);//"- This, a sample string.";
  char *arg = strtok(str," ");
  char *option;
   while(arg != NULL)
 {
   
   option=strtok(NULL, " ");
    setSingleExecutionArgument(arg, option);
    arg=option;
   }
}

int
Ctable::setSingleExecutionArgument(char *arg, char *option){  
  int ret=0;

       if (isdigit(arg[0])){
	cmodels.param.many = atoi(arg);
	  }else
      if (arg[0] == '-'){
	if (strcmp (&arg[1], "rs") == 0){
	  cmodels.param.sys = RELSAT;
	  //			cmodels.param.loopFormula = true;
			
	}	
	else if(strcmp (&arg[1], "file") == 0){
	  if(option==NULL){
	    usage();
	    exit(1);
	  }
	  strcpy(cmodels.param.file, &option[0]);
	  ret=1;
	}
	else if (strcmp (&arg[1], "dimacs") == 0)
	  cmodels.param.sys =  DIMACS_PRODUCE;
	else if (strcmp (&arg[1], "cdimacs") == 0)
	  cmodels.param.sys =  CASP_DIMACS_PRODUCE;
	else if (strcmp (&arg[1], "zc") == 0)
	  cmodels.param.sys = ZCHAFF;	
	else if (strcmp (&arg[1], "zca") == 0)
	  cmodels.param.sys = ASSAT_ZCHAFF;	
	else if (strcmp (&arg[1], "ms") == 0)
	  cmodels.param.sys = MINISAT;	
	else if (strcmp (&arg[1], "ms1") == 0)
	  cmodels.param.sys = MINISAT1;	
	else if (strcmp (&arg[1], "bc") == 0)
	  cmodels.param.sys =  BCIRCUIT;

	else if (strcmp (&arg[1], "si") == 0){
	  cmodels.param.sys = SIMO; 
	}
	else if (strcmp (&arg[1], "sb") == 0){
	  cmodels.param.sort = true; 
	}
	else if (strcmp (&arg[1], "atomreason") == 0){
	  cmodels.param.loopFormula = false; 
	}
	else if (strcmp (&arg[1], "loopformula1") == 0){
	  cmodels.param.loopFormula1 = true; 
	}
	else if (strcmp (&arg[1], "temp") == 0){
			cmodels.param.temp = true; 
	}
	else if (strcmp (&arg[1], "version") == 0){
	  cout<<"Version "<<CMODELS_VERSION<<"\n";
	  exit(0); 
	}
	else if (strcmp (&arg[1], "eloop") == 0){
	  cmodels.param.eloop = true; 
	}
	else if(strcmp (&arg[1], "statistics") == 0)
	  cmodels.output.stat= true;
	else if (strcmp (&arg[1], "w") == 0)
	  cmodels.param.cm_wfm = true;	
	
	else if(strcmp (&arg[1], "dlp") == 0 | 
		strcmp (&arg[1], "-dlp") == 0 ){
	  cmodels.program.disj= true;
	  cmodels.program.disjProgramLparse=true;
	}
	else if(strcmp (&arg[1], "verify") == 0){
	  numberExpected(option);
	  int method= atoi(&option[0]);
	  if(method==0)
	    cmodels.param.verifyMethod=MIN;
	  if(method==1)
	    cmodels.param.verifyMethod=MINSCC;
	  if(method>1|method<0)//default then
	    cmodels.param.verifyMethod=MINSCC;
	  ret=1;
	}
	//	  else if(strcmp (&arg[1], "s") == 0)
	//	cmodels.param.wf= false;
	else if(strcmp (&arg[1], "printCycle") == 0)
	  cmodels.param.printCycle= true;
	else if(strcmp (&arg[1], "out_f_c") == 0){
	  cmodels.output.out_f_c= true;
	}
	else if(strcmp (&arg[1], "timings") == 0)
	  cmodels.output.timings= true;
	else if(strcmp (&arg[1], "silent") == 0){
	  cmodels.output.asparagus= SILENT; //program should not output res onlytime 
	  
	}
	else if(strcmp (&arg[1], "asparagus") == 0){
	  cmodels.output.asparagus= ASPARAGUS; //program should output in asparagus format
	}
	else if(strcmp (&arg[1], "asp2") == 0){
	  cmodels.output.asparagus= ASPCOMP2; //program should  output in 3d asp competition format
	  
	}
	
	else if(strcmp (&arg[1], "onlytime") == 0){
	  cmodels.output.asparagus= SILENT; //program should not output res onlytime 
	  
	}
	else if(strcmp (&arg[1], "ext") == 0){
	  if(option==NULL){
	    usage();
	    exit(1);
	  }
	  cmodels.param.dir= true;
	  strcpy(cmodels.param.dirName,&option[0]);
	  ret=1;
	}else if(strcmp (&arg[1], "forget-percent") == 0){
	  numberExpected(option);
	  cmodels.param.forgetPercent=atoi(&option[0]);
	  if (cmodels.param.forgetPercent<0||cmodels.param.forgetPercent>100){
	    cout<<"Warning: -forget-percent is set to default 0 as its specified value should range between 0 and 100 whereas it is sat to "<<&option[0]<<endl; 
	    cmodels.param.forgetPercent=0;
	  }
	  ret=1;
	}
	else if(strcmp (&arg[1], "timeout") == 0){
	  numberExpected(option);
	  cmodels.param.timeout = atoi(&option[0]);
	  //strcpy(cmodels.dirName,&argv[c+1][0]);
	  ret=1;
	}
	else if(strcmp (&arg[1], "heur") == 0){
	  numberExpected(option);
	  cmodels.param.heur = atoi(&option[0]);
	  //strcpy(cmodels.dirName,&argv[c+1][0]);
	  ret=1;
	}
	else if(strcmp (&arg[1], "config") == 0){
	  if(option==NULL){
	    usage();
	    exit(1);
	  }
	  strcpy(cmodels.param.config, &option[0]);
	  ret=1;
	}
	else if(strcmp (&arg[1], "numlf") == 0){
	  numberExpected(option);
	  cmodels.param.numLFClauses = atoi(&option[0]);
	  //strcpy(cmodels.dirName,&argv[c+1][0]);
	  ret=1;
	}else if(strcmp (&arg[1], "keep") == 0){
	  cmodels.param.keep= true;
	  
	}	
	else if(strcmp (&arg[1], "bt") == 0){
	  cmodels.param.bt= true;
	  cmodels.param.le= false;
	}	
	else if(strcmp (&arg[1], "bj") == 0){
	  cmodels.param.bj= true;
	  cmodels.param.le= false;
	}		  
	else if(strcmp (&arg[1], "le") == 0){
	  cmodels.param.le= true;
	}
	else if(strcmp (&arg[1], "modes") == 0){		
	  cmodels.param.bmodes= true;
	}	
	else if(strcmp (&arg[1], "shortr") == 0){		
	  cmodels.param.shortr= true;
	}	
	else if(strcmp (&arg[1], "hf") == 0){		
	  cmodels.param.hf= true;
	}	
	else{ 
	  usage();
	  exit(1);
	} 
      }
      else{
	  usage();
	  exit(1);
      }
	  
       return ret;

}

void
Ctable::numberExpected(char* option){
  if(option==NULL||!isdigit(option[0])){
    usage();
    exit(1);
  }	  
}

int 
Ctable::getNumberGroundedAtoms(){
  return cmodels.program.original_number_of_atoms;
}

void 
Ctable::Initialize(int* answerset_lits, int& num_atoms, const char **&symbolTable, int &symbolTableEntries){
  cmodels.output.asparagus= SILENT;
  cmodels.init(answerset_lits, num_atoms,symbolTable,symbolTableEntries);
  //  cout<<"After initialize: num_atoms: "<<num_atoms<<endl;
  if(num_atoms>=-1)
    solved=true;
  else 
    solved=false;
}

void 
Ctable::Initialize(int* answerset_lits, int& num_atoms){
  const char **symbolTable;
  int symbolTableEntries;

  Initialize(answerset_lits,num_atoms,symbolTable,symbolTableEntries);
  
}

void
Ctable::setTestPartialSolutionInfo(testPartialSolutionInfo *tpsi) { /* [marcy 022812] */
	cmodels.setTestPartialSolutionInfo(tpsi);
}

bool 
Ctable::addDenial (int* constraint_lits, int num_lits){
  //  print_lits(constraint_lits, num_lits,true);
  return cmodels.addDenial(constraint_lits, num_lits);
}
void
Ctable::Solve(int* answerset_lits, int& num_atoms){
  //  cout<<"Cmodels Solving \n";
  if(solved){
    //cout<<"Have been solved in initialize on the first call -- so a denial of the first model will kill that only answer set so we return unsat"<<endl;
    num_atoms=-1;
    return;
  }
  cmodels.singleSolve(answerset_lits, num_atoms);
  //  print_lits(answerset_lits, num_atoms,false);
}

void
Ctable::print_lits(int* constraint_lits, int num_lits, bool denial){
  int cur;
  bool cur_sign;
  int inner_count=0;
  long indA=0;
 
  if(!denial){
    cout<<"Solution: ";
  }
  else 
    cout<<"Denial: :- ";
  
  for (int i=0; i<num_lits; i++){
    if(!denial){
      cur=constraint_lits[i];
      cur_sign=true;
    }else{
      if(constraint_lits[i]%2){//if it is odd      
	cur=(constraint_lits[i]-1)/2;
	cur_sign=true;
      }
      else{
	cur=constraint_lits[i]/2;
	cur_sign=false;
      }
    }
    
    for(indA=inner_count; indA<cmodels.program.cmodelsAtomsFromThisId; indA++){
      
      if(cur==cmodels.program.atoms[indA]->get_lparse_id()){
	
	if(cur_sign)
	  cmodels.program.atoms[indA]->print();
	else{
	  cout<<"-";
	  cmodels.program.atoms[indA]->print();
	}
	cout<<", ";
  
	break;
      }
    }
    if(indA==cmodels.program.cmodelsAtomsFromThisId-1&&i!=num_lits-1){
      cerr<<"Cmodels: Error with denial print ";
      exit(20);
    }

  }
  cout<<" done."<<endl;

}

void
Ctable::markExternallyConstrainedAtoms(int* answerset_lits, int& num_atoms, bool* trueExternal){
  //recall that external atoms propagators are only allowed in Minisat1 mode
  if (cmodels.param.sys!=MINISAT1){
	cerr<<"This functionality is supported only for MINISAT1 -ms1 option";
	exit(0);
	  }
  cmodels.markExternallyConstrainedAtoms(answerset_lits, num_atoms, trueExternal);
}

void
Ctable::calculate()
{
  cmodels.cmodels();
}
void 
Ctable::usage ()
{
  cerr << "Usage: cmodels [number] [-dlp] [-si] [-zc]  [-rs]  [-verify number] [-s] [-ext <string>] [-statistics] [-config name_config_file]"
       << endl << "[-dlp] disjunctive logic program ( '|' is used for disjunction   a1 | a2 | ... | an :- body. or  { a(X) : b(X) } :- body. Choice rules are forbidden) Used when lparse is called with -dlp flag."
	   <<endl<< "[-version] prints out the version number"
	<< endl << "[-ms] minisat v. 2 to call (default)"	
       << endl << "[-zc] zchaff to call  "           
	<< endl << "[-ms1] minisat v. 1 to call "
	   << endl << "[-si] simo to call " 
       << endl << "[-rs] relsat vs.2 to call"
	   << endl << "[number] number of models of completion to compute"
	   << endl << "0 - stands for all, 1 is default"	
	   << endl << "[-verify number] for disjunctive programs verifies that solution is an answer set using GNT-method 0, GNT-method-enhanced by modularity as in DLV 1(default)"
	   << endl << "[-atomreason] build reason from some atoms of loop formula"
	   << endl << "[-loopformula1] build and add only one loop formula at a time (default all found loop formulas, i.e., per each SCC)"
	   << endl << "[-temp] relevant only to ms1 (minisat vs 1), added loop formulas may be forgot with the time"

	//	   << endl << "[-eloop] build  loop formula from elementary loop"
	   << endl << "[-numlf <number>] how many clauses loop formula is allowed to be, if this number is larger then only part of loop formula is added"
	   << endl << "[-sb] identifies rules with same bodies; creates one auxiliary atom to represent this body"
<< endl << "[-forget-percent number] in case of incremental solving with minisat1 at added denial (constraint will forget <number> percent of learnt clauses previously"
       << endl << "[-config name_config_file] name of configuration file, CONFIG is default" 

	   << endl << "[-ext <string>] starts intermediate files with  specified extension <string>"
	   << endl << "[-keep] keeps intermediate files "

	// << endl << "[-mcnorep] in case of mchaff invocation removes repetitions in the solutons "
	 
	   << endl << "[-out_f_c] solutions located into OUT* file"
           << endl << "[-statistics] print out statistics"
	//           << endl << "[-s] -wfm"
       << endl << "SAT solver Simo related options: "
     << endl << "[-le] Simo performs backjumping and learning "
     << endl << "[-bj] Simo performs backjumping"
	   << endl << "[-heur number] number (integer) specifies the heuristic Simo uses while doing the search. "	   
<< endl << "[-w] instructs Cmodels to compute well-founded model and exit "
<< endl << "[-file <string>] instructs Cmodels to consider file named <string> as input (file should be in lparse/gringo format"
<< endl << "[-dimacs] instructs Cmodels to produce DIMACS file containing clausified completion and exit "
<< endl << "[-cdimacs] instructs Cmodels to produce DIMACS file containing clausified completion where atoms carry the names from original problem statement and exit ";

}

;


