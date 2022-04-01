/* =========FOR INTERNAL USE ONLY. NO DISTRIBUTION PLEASE ========== */

/*********************************************************************
 Copyright 2000-2001, Princeton University.  All rights reserved. 
 By using this software the USER indicates that he or she has read, 
 understood and will comply with the following:

 --- Princeton University hereby grants USER nonexclusive permission 
 to use, copy and/or modify this software for internal, noncommercial,
 research purposes only. Any distribution, including commercial sale 
 or license, of this software, copies of the software, its associated 
 documentation and/or modifications of either is strictly prohibited 
 without the prior consent of Princeton University.  Title to copyright
 to this software and its associated documentation shall at all times 
 remain with Princeton University.  Appropriate copyright notice shall 
 be placed on all software copies, and a complete copy of this notice 
 shall be included in all copies of the associated documentation.  
 No right is  granted to use in advertising, publicity or otherwise 
 any trademark,  service mark, or the name of Princeton University. 


 --- This software and any associated documentation is provided "as is" 

 PRINCETON UNIVERSITY MAKES NO REPRESENTATIONS OR WARRANTIES, EXPRESS 
 OR IMPLIED, INCLUDING THOSE OF MERCHANTABILITY OR FITNESS FOR A 
 PARTICULAR PURPOSE, OR THAT  USE OF THE SOFTWARE, MODIFICATIONS, OR 
 ASSOCIATED DOCUMENTATION WILL NOT INFRINGE ANY PATENTS, COPYRIGHTS, 
 TRADEMARKS OR OTHER INTELLECTUAL PROPERTY RIGHTS OF A THIRD PARTY.  

 Princeton University shall not be liable under any circumstances for 
 any direct, indirect, special, incidental, or consequential damages 
 with respect to any claim by USER or any third party on account of 
 or arising from the use, or inability to use, this software or its 
 associated documentation, even if Princeton University has been advised
 of the possibility of those damages.
*********************************************************************/
#include <iostream>
#include <fstream>
#include <cstdlib>
#include <cstdio>

#include <set>
#include <vector>

#include "SAT.h"

using namespace std;

#define MAX_LINE_LENGTH    65536
#define MAX_WORD_LENGTH    64

//This cnf parser function is based on the GRASP code by Joao Marques Silva
void read_cnf(SAT_Manager mng, char * filename )
{
    char line_buffer[MAX_LINE_LENGTH];
    char word_buffer[MAX_WORD_LENGTH];
    set<int> clause_vars;
    set<int> clause_lits;
    int line_num = 0;

    ifstream inp (filename, ios::in);
    if (!inp) {
	cerr << "Can't open input file" << endl;
	exit(1);
    }
    while (inp.getline(line_buffer, MAX_LINE_LENGTH)) {
	++ line_num;
	if (line_buffer[0] == 'c') { 
	    continue; 
	}
	else if (line_buffer[0] == 'p') {
	    int var_num;
	    int cl_num;

	    int arg = sscanf (line_buffer, "p cnf %d %d", &var_num, &cl_num);
	    if( arg < 2 ) {
		cerr << "Unable to read number of variables and clauses"
		     << "at line " << line_num << endl;
		exit(3);
	    }
	    SAT_SetNumVariables(mng, var_num); //first element not used.
	}
	else {                             // Clause definition or continuation
	    char *lp = line_buffer;
	    do {
		char *wp = word_buffer;
		while (*lp && ((*lp == ' ') || (*lp == '\t'))) {
		    lp++;
		}
		while (*lp && (*lp != ' ') && (*lp != '\t') && (*lp != '\n')) {
		    *(wp++) = *(lp++);
		}
		*wp = '\0';                                 // terminate string

		if (strlen(word_buffer) != 0) {     // check if number is there
		    int var_idx = atoi (word_buffer);
		    int sign = 0;

		    if( var_idx != 0) {
			if( var_idx < 0)  { var_idx = -var_idx; sign = 1; }
			clause_vars.insert(var_idx);
			clause_lits.insert( (var_idx << 1) + sign);
		    } 	
		    else {
			//add this clause
			if (clause_vars.size() != 0 && (clause_vars.size() == clause_lits.size())) { //yeah, can add this clause
			    vector <int> temp;
			    for (set<int>::iterator itr = clause_lits.begin();
				 itr != clause_lits.end(); ++itr)
				temp.push_back (*itr);
			    SAT_AddClause(mng, & temp.begin()[0], temp.size() );
			}
			else {} //it contain var of both polarity, so is automatically satisfied, just skip it
			clause_lits.clear();
			clause_vars.clear();
		    }
		}
	    }
	    while (*lp);
	}
    }
    if (!inp.eof()) {
	cerr << "Input line " << line_num <<  " too long. Unable to continue..." << endl;
	exit(2);
    }
//    assert (clause_vars.size() == 0); 	//some benchmark has no 0 in the last clause
    if (clause_lits.size() && clause_vars.size()==clause_lits.size() ) {
	vector <int> temp;
	for (set<int>::iterator itr = clause_lits.begin();
	     itr != clause_lits.end(); ++itr)
	    temp.push_back (*itr);
	SAT_AddClause(mng, & temp.begin()[0], temp.size() );
    }
    clause_lits.clear();
    clause_vars.clear();
}


void handle_result(SAT_Manager mng, int outcome, bool * assignments )
{
    char * result = "UNKNOWN";
    switch (outcome) {
    case SATISFIABLE:
	cout << "Instance satisfiable" << endl;
//following lines will print out a solution if a solution exist
	for (int i=1, sz = SAT_NumVariables(mng); i<= sz; ++i) {
	    switch(SAT_GetVarAsgnment(mng, i)) {
	    case -1:	
		cout <<"("<< i<<")"; 
		assignments[i-1]=false;
		break;
	    case 0:
		cout << "-" << i; 
		assignments[i-1]=false;
		break;
	    case 1:
		cout << i ; 
		assignments[i-1]=true;
		break;
	    default:
		cerr << "Unknown variable value state"<< endl;
		exit(4);
	    }
	    cout << " ";
	} 
	result  = "SAT";
	cout << endl;
	break;
    case UNSATISFIABLE:
	result  = "UNSAT";
	cout << "Instance unsatisfiable" << endl;
	break;
    case TIME_OUT:
	result  = "ABORT : TIME OUT"; 
	cout << "Time out, unable to determing the satisfiablility of the instance";
	cout << endl;
	break;
    case MEM_OUT:
	result  = "ABORT : MEM OUT"; 
	cout << "Memory out, unable to determing the satisfiablility of the instance";
	cout << endl;
	break;
    default:
	cerr << "Unknown outcome" << endl;
	exit (5);
    }	

    cout << "Num. of Variables\t\t\t" << SAT_NumVariables(mng) << endl;
    cout << "Original Num Clauses\t\t\t" << SAT_InitNumClauses(mng) << endl;
    cout << "Original Num Literals\t\t\t" << SAT_InitNumLiterals(mng) << endl;
    cout << "Deleted Unrelevant clause\t\t" << SAT_NumDeletedClauses(mng) <<endl;
    cout << "Deleted Unrelevant literals\t\t" << SAT_NumDeletedLiterals(mng) <<endl;

}
void output_status(SAT_Manager mng)
{
    cout << "Dec: " << SAT_NumDecisions(mng)<< "\t ";
    cout << "AddCl: " << SAT_NumAddedClauses(mng) <<"\t";
    cout << "AddLit: " << SAT_NumAddedLiterals(mng)<<"\t";
    cout << "DelCl: " << SAT_NumDeletedClauses(mng) <<"\t";
    cout << "DelLit: " << SAT_NumDeletedLiterals(mng)<<"\t";
    cout << "NumImp: " << SAT_NumImplications(mng) <<"\t";
    cout << "AveBubbleMove: " << SAT_AverageBubbleMove(mng) <<"\t";
    //other statistics comes here
    cout << "RunTime:" << SAT_GetElapsedCPUTime(mng) << endl;
}

void verify_solution(SAT_Manager mng)
{
    int num_verified = 0;
    for ( int cl_idx = SAT_GetFirstClause (mng); cl_idx >= 0; 
	  cl_idx = SAT_GetNextClause(mng, cl_idx)) {
	int len = SAT_GetClauseNumLits(mng, cl_idx);
	int * lits = new int[len+1];
	SAT_GetClauseLits( mng, cl_idx, lits);
	int i;
	for (i=0; i< len; ++i) {
	    int v_idx = lits[i] >> 1;
	    int sign = lits[i] & 0x1;
	    int var_value = SAT_GetVarAsgnment( mng, v_idx);
	    if( (var_value == 1 && sign == 0) ||
		(var_value == 0 && sign == 1) ) break;
	}
	if (i >= len) {
	    cerr << "Verify Satisfiable solution failed, please file a bug report, thanks. " << endl;
	    exit(6);
	}
	delete [] lits;
	++ num_verified;
    }
    cout << num_verified << " Clauses are true, Verify Solution successful. ";
}
void loadCnfFiletoZchaff(SAT_Manager mng, char * filename)
{
    read_cnf (mng, filename);
}
/* if you want some statistics during the solving, uncomment following line */
//    SAT_AddHookFun(mng,output_status, 5000);


int main(){
 SAT_Manager mng = SAT_InitManager();
 loadCnfFiletoZchaff(mng, "cnf.out");
 int result = SAT_Solve(mng);
 if (result == SATISFIABLE) 
   verify_solution(mng);
 else{
   cout<<"UNSAT"<<endl;
 }
 int numLiterals= SAT_NumVariables(mng);
 cout<<"SAT_NumVariables(mng): "<<SAT_NumVariables(mng);
 bool*  assignments = new bool [numLiterals];  
 // bool* copyassignments = new bool [program->number_of_atoms];  
 handle_result (mng, result,  assignments); //rewrite handle_result
    //in the same manner simo does
 
 int clause[1];
 clause[0]=3;
 SAT_AddClause(mng, clause, 1);
 SAT_Reset(mng);
 result =SAT_Solve(mng);
 if (result == SATISFIABLE) 
   verify_solution(mng);
 else{
   cout<<"UNSAT"<<endl;
 }
 numLiterals= SAT_NumVariables(mng);
 cout<<"SAT_NumVariables(mng): "<<SAT_NumVariables(mng);
  // bool* copyassignments = new bool [program->number_of_atoms];  
 handle_result (mng, result,  assignments); //rewrite handle_result
    //in the same manner simo does
 
 return 0;
}


















