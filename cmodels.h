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
// yuliya@cs.utexas.edu
#ifndef CMODELS_H
#define CMODELS_H

#include "program.h"
#include "graphscc.h"
//#include "wf.h"
#include "api.h"
#include "interpret.h"
#include <vector>
#include "MiniSat_v1.12b/Solver.h"

using namespace std;
class Atom;


class Cmodels
{
public:
  Cmodels ();
  virtual ~Cmodels ();
  Program program;
  Output output;
  Param param; //contains all the fields with parameters
               //that may be initialized at command line


  Api *api;
  
  
  Atom* false_atom; //atom that is false (used in constraints or later)
  Atom* true_atom;  //atom that is true introduced by cmodels 
  
  vector<int> LRVarIDs;//stores all the IDs of Level Ranking Variables in order to add cspvar(lr)
  	  	  	  	  	   //LRVarIDs[ID]=1, if the Level Ranking Variable with this ID exists

  void * satMngMinimality;
  void * zchaffMng;

  SimpSolver* minisatSolver; //minisat solver
  ms1::Solver* mSolver1; //minisat solver


 



  //we need these in case if sat solver is called from outside
  char command[512];




  void cmodels(); //runs translation invokation and so on
  bool addDenial(int* constraint_lits, int num_lits);
  void markExternallyConstrainedAtoms (int* constainted_ayoms, int num_atoms, bool* trueExternal);
  void singleSolve(int* answerset_lits,  int& num_atoms);
  void init(int* answerset_lits, int& num_atoms, const char **&symbolTable, int &symbolTableEntries);
  void setTestPartialSolutionInfo(testPartialSolutionInfo *tpsi); /* [marcy 022812] */

protected:
  Atom*** rec_buf_atoms; //recuired for the translation of card. constraints in polynomial time
  // Atom*** rec_wbuf_atoms; //recuired for the translation of card. constraints in polynomial time
  bool rec_weight_rule(Weight totalweight, 
					   int sizeC, 
					   Atom* headC,
					   unsigned long atleast, 
					   int counter_body);

  
  //*****************



  Graph* grCC;
  bool solutionVerification(bool* assignment, list<Atom*>& mminus );
  void buildReduct();
  void findCons();
  void printCycles(const int&numSCC);
  void printCons();
  void printM();
  void printWFM();
  void printMminus();
  //if consdisj passed then mminus marked by consdisj assgnments
  //if it is not passed then mminus is diffence between inM and Cons
  void findMminus(bool* = 0);


  bool translate_all_to_nested_rules();
  void eraseFalseAtomsFromClauses();

  void add_fact_rule(Atom* a);
  
  inline void add_clause_from_compute (Atom *a, bool  pos);
  inline void releaseSolvers();
  void createCompletion(); 
  void createRankingFormula();
  void createStrongRankingFormula(long curAtomsSize,string NumOfAtom);
  void createSCCRankingFormula();
  void createStrongSCCRankingFormulaCondition3(vector<list<Atom*>*>* NTSCCs);
  Result createClauses();
  void createSingleAtomClauses();

  void createDoubleClause(Atom* firstAtom,Atom* secAtom,bool firstTrue,bool secTrue);

  void createFalseHeadClauses(Atom* a);  

  // we will find the situations such that _false<-int1
  //                                       int1<-...hello_...
  // it is eq to false<-...hello_...       
  // so in all the atoms like int1 we will put the flag atom->false_atom = true and build 
  // completion respectivly
  // and also we will creat the clauses for _fales 
  // like createFalseHeadClauses(Atom* a) does



  bool print_output_for_sat();// populates Clause databases of different solvers
                              // or calls to create dimacsxxx.out file standard for various solvers

  void print_DIMACS(); //creates dimacsxxx.out file standard for various solvers
                       //      or smt-dimacs.out for smt-connection



  void print_output_for_BCircuit();//creates cmodels.out which is circuit description

  void print_completion();
  void print_clauses();


  Result call_satSolver();
  Result preprocessing(bool& emptyprogram);




  void loadClausesToZchaffManager();

  //add clauses performs simplifications 
  //within minisat
  //therefore it can not that the formulas is UNSAT
  //and return false
  bool loadClausesToMinisat(bool=true);//either permanent or learn
  //loop formulas can be learned for time only
  void addReasonClause(int* reason);
  void print_time();

  Result call_relsat();
  Result call_assat_zchaff();


  


  void printReason(int* assignment, int found);
  void printSolution(bool* assignment, int found);
  bool checkSolutions(bool* assignments, list<Atom*>& mminus );
  void findLFReason(bool* assignment, int* reason, int & reasonSize, list<Atom *>& mminus, int* =0);

  void loopRulesInit(const int& numSCC, 
					 vector<Atom*>* atomsSCC,
					 vector<NestedRule*>* rulesOfLoopsHeads);
  void loopRulesInitSCC( vector<Atom*>& atomsSCC,
					 vector<NestedRule*>& rulesOfLoopsHeads);
  void buildClausesOfLoopFormula(const vector<Atom*> & atomsSCC,
								 const  vector<NestedRule*> & rulesOfLoop);


  void printRules(vector<NestedRule*>& rules);

  void printAtoms(vector<Atom*>& atoms);
  void printAtoms(list<Atom*>& atoms);
  void buildReasonFromLoops(const vector<Atom*>& atomsSCC,
						   int* reason, 
						   const vector<NestedRule*>& rulesOfLoopsHeads,
						   const int& inLoop,
						   int* =0);
 //returns Number of Loopformulas build
  Result call_simo();
  Result call_zchaff();
  Result call_minisat();

  void translateClauseToReason(int* reason, int & reasonSize);
  void addAssignmentClause(bool* assignments);
  void addAssignmentClauseForMinVerification(bool* assignments);
  void addAssignmentToCmodelsOut(bool* assignments);

  
  void copyBasicRuleHead(BasicRule *rfrom, Completion *rto);


  //hear for adding rules like -hvh for choice rules
  void add_tautology_clause(Atom* head);


  //for translation of constraint rules to basic rules  
  
  void copyCBody(Completion* comp);
  void copyBasicRuleBody(BasicRule *rfrom, Completion *rto);
  void print ();  // prints out the rules calls program->print()

 //take care of sim0plifing rules which have WFS atoms in their
  bool walk_nbody_to_add_body(Rule *r);
  bool walk_pbody_to_add_body(Rule *r);
  void walk_nbody_constraintrule_to_add_body(ConstraintRule *r);
  void walk_pbody_constraintrule_to_add_body(ConstraintRule *r);
  void walk_body_weightrule_to_add_body(WeightRule *r);
  bool walk_to_add_head(DisjunctionRule* r);
  //places atoms marked by Mminus into Mminus array
  void getMminus(list<Atom*>& Mminus);

  void markAtomsInSccInM(const int & sccid);
  void markAtomsInM( bool *sol);
  void markAtomsInCons(vector<Atom*> &atomsSCC,bool *sol );
  void markAtomsInCons(bool *sol );
  void clearAtomsInCons(vector<Atom*> &atomsSCC);
  void clearInLoop();
  void clearInLoop(vector <Atom*>* atomsSCC, const long & numSCC);
  void clearInMminus();
  void clearInM();
  void clearInMminus(list<Atom*>& mminus);

  void findAllEsets(list<vector<Atom*> > & elSets, vector<Atom*> atomsSCC, long numSCC);
  bool checkFoundnessElset(list<Atom*>& restelSet, const int& sccId);
  //if second parameter is false
  //then we build a complete graph diregarding if body
  //is true wrt the model or false
  //If the second parameter is default true
  //then we pay attention to the model
  void  buildGraphsCCandReverse( list<Atom*>& mminus,const bool & wrtModel); //returns number of vertices in CCgraph
  void buildCompletePosNegGr(list <Atom*> & mminus);

  void findSCC(long* atomCC,list<Atom*>& mminus, long & numSCC, bool posDependency, const bool & wrtModel);




 
 
  void populate_answerset_lits_wfm(int* answerset_lits, int& num_atoms);

  void reasonSolverTime();

  
  void createModelVerificationManager();
  void createModelVerificationManagerMin(vector<Atom*> &atomsSCC);



  int extendModelVerificationManager(bool* assignment);


  Timer solverTimer;
  Timer reasonTimer;
  // Timer preprocessingTimer;
  // Timer postprocessingTimer;

  //Functions for disjunctive case
  Atom* createAuxAtom(Atom* head,NestedRule* cr);  
  


  //Create auxiliary atom for conjunctions in level ranking formula.
  Atom* createAuxAtom2(Atom* head,NestedRule* cr);
  //Create auxiliary atom for conjunctions in level ranking formula. And set isRR.
  void createAuxAtomSCC(NestedRule* cr,list<Atom*>* SCC);
  //Create auxiliary atom for (a and body) in the head of completion in strong level ranking formula condition 3.
  Atom* createAuxAtomHeadBody(Atom* head,NestedRule* cr);
  void markNestedRule(NestedRule* cr);
  void createRepresentative(NestedRule* cr);
//Creates Body imlies Head clause
  void createNestedRuleBodyAClause(NestedRule *r);
 
  bool minTestGnt(bool *assignment, list<Atom*>& mminus );
  bool testMinSCC(vector<Atom*>& atomsSCC);
  // function computes loop formula or reason based on:
  // assignment, atoms within which mminus is located (mminus)
  // it stores reason and reasonsize in the corresponding arguments
  void LoopFormulaComputation(int* reason, int & reasonSize, 
							  list<Atom*> & mminus , int * =0);


  void findMarkSCC(bool* assignment, int &numSCC);


  // based on set of atoms in mminus, 
  // finds SCC in induced positive dependency graph by Mminus
  // marks such atoms in their .inLoop
  // and returns array that says how may atoms in each SCC
  // number of SCC is returned in numSCC 
  void enumMarkSCC( list<Atom*>& mminus, long & numSCC, bool posDependency, bool = true);

  void atomsMultiplication(const vector<NestedRule*> & rules, 
						   const int& numRules,  
						   int curRule,  
						   int & counter,
						   const int& inLoop);
  void clean();
  void setupFilenames();

  void placeToApi(Atom** start, Atom** end, bool truth);
  void resetApi();
  void resetCompApi();
  void clauseFromApi();

  //HCF related things
  bool dlvOperatorCondition(Atom* atom);
  void aproxMminus(list<Atom*>& mminusAtoms);
  void markInMminus(list<Atom*>& mminusAtoms);
  void markInMminus(vector<Atom*>& mminusAtoms);
  bool hcfTest(bool* assignment, list<Atom*>& mminus );
  void setInLoopId(vector<Atom*>& atomsSCC);
  //  void resetInLoopId(vector<Atom*>& atomsSCC);
  bool HCFverification(const int & numSCC);
  bool HCFverificationSCC(const vector<Atom*>&atomsSCC, const int& sccId);

  void markProgramsSCC(long & numSCC, bool posDependency);//finds SCCs of the program
  void initPBodyRules();
  void activeElementaryLoop(list<Atom*>& elSet, const int& sccId);
  void addPriorityQ(list<Atom*> & Q, Atom* p);
  void printRules();
  void printRules(Atom* a);
  void copyVectorToList(vector<Atom*>& from, list<Atom*>& to);
  void copyListToVector(list<Atom*>& from, vector<Atom*>& to);
  void copyVectorToList(vector<Rule*>& from, list<Rule*>& to);
  void copyListToVector(list<Rule*>& from, vector<Rule*>& to);

  void clearInExp(list<Atom*>& mminus);
  void clearInAct(list<Atom*>& mminus);
  void clearInLoopId(list<Atom*>& mminus);
  bool wellFounded();
  void initRuleLists4WF();
  void sortRules();
  void findSameBodies();
  bool completeWFM();
  bool pt();

  Result call_solver_for_answer_sets();
  Result call_incr_solver(bool* assignments);
Result incr_solver_test();
}
;
#endif
