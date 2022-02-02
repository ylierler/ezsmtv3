// SIMO: Satisfiability Internal Module (Object oriented version)
// Version 3.0
// Copyright (C) 2000-2002 Enrico Giunchiglia, Marco Maratea, Armando Tacchella
// 
// This library is free software; you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public
// License as published by the Free Software Foundation; either
// version 2.1 of the License, or (at your option) any later version.
// 
// This library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// Lesser General Public License for more details.
// 
// You should have received a copy of the GNU Lesser General Public
// License along with this library; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
// 
//  For any questions regarding SIMO send e-mail to: sim@mrg.dist.unige.it

// simo.cpp

// #include "Solver.h"
#include "simo.h"
#include "defines.h"
// Return values
#define RET_UNKNOWN        0
#define RET_SATISFIABLE   10
#define RET_UNSATISFIABLE 20

// Global pointer to SAT instance
Solver * SATinstance;
//SIMO * SAT;
// Prototypes
static void loadInstance(int argc, char * argv[]);
static void EventHandler(int sig);


// Instance loading and params parsing
//  void loadInstance(int argc, char * argv[])
//  {
//    FILE* inFile;

//    // The instance is the first argument
//    if ((inFile = fopen(argv[1], "r")) != NULL) {
//      SATinstance = new Solver(inFile);
//      fclose(inFile);
//    } else {
//      fclose(inFile);
//      exit (RET_UNKNOWN);
//    }

//    // Install timeout handler
//    SATinstance->SetTimeoutHandler(EventHandler);

//    // The random seed is the (optional) second argument
//    // All the other arguments follow
//    if (argc > 2) {
//      char ** tmpArgv = new char*[argc];
//      tmpArgv[0] = argv[0];
//      tmpArgv[1] = new char[8];
//      sprintf(tmpArgv[1], "+seed");
//      tmpArgv[2] = argv[2];
//      if (argc > 3) {
//        for (int i = 3; i < argc; i++) {
//  	tmpArgv[i] = argv[i];
//        }
//      }
//      SATinstance->SetOptions(argc, tmpArgv);
//      delete[](tmpArgv[1]);
//      delete[](tmpArgv);
//    }

//    return;
//  }


// Instance loading and params parsing
void loadInstance(char * nomefile, bool erase)
{
  FILE* inFile;

  // The instance is the first argument
  if ((inFile = fopen(nomefile, "r")) != NULL) {
    SATinstance = new Solver(inFile, erase);
    fclose(inFile);
  } else {
    fclose(inFile);
    exit (RET_UNKNOWN);
  }

  // Install timeout handler
  SATinstance->SetTimeoutHandler(EventHandler);


  return;
}


static void EventHandler(int sig)
{
  switch (sig) {

#ifndef _WIN32	// marcy
  case SIGXCPU:
#ifndef SHORT_OUT
    SATinstance->PrintStatsDimacs(UNKNOWN);
#else
    SATinstance->PrintStats( UNKNOWN);
#endif
    delete(SATinstance);
    break;
#endif
  default:
    fprintf(stderr, "Unknown event\n");
    break;
  }

  exit (RET_UNKNOWN);
}

// clause.cpp

/******************************************************************************
 * Standard and user-defined includes					   
 *****************************************************************************/
// #include "Clause.h"
// #include "Solver.h"

/*****************************************************************************/
/*! default constructor
 *
 *  \param  none
 */
/*****************************************************************************/
Clauses::Clauses()
{
  _id = _size = 0; 
  _base = 0;

  return;
} // End of Clause::Clause()


/*****************************************************************************/
/*! clause constructor
 *
 *  \param id       clause identifier.
 *  \param capacity maximun number of storable literals without reallocation.
 */
/*****************************************************************************/
Clauses::Clauses(int id, int capacity)
{
  _id = id;
  _size = 0;
  // Allow two more elements for clause markers
  _base = (new Literal[capacity + 2]) + 1;

  return;
} // End of Clause::Clause(int id, int capacity)


/*****************************************************************************/
/*! clause constructor
 *
 *  \param res1   first resolvent.
 *  \param res2   second resolvent.
 *  \param varId  resolved variable.
 */
/*****************************************************************************/
Clauses::Clauses(ClauseRef res1, ClauseRef res2, int varId)
{


  // This is a conflict-generated clause
  _id = _size = 0;

  // capacity allows two more elements for clause markers
  _base = (new Literal[res1->_size + res2->_size]) + 1;
  LiteralRef curr = _base;

  // Sorted merge of literals
  LiteralRef l1 = res1->_base;
  LiteralRef l2 = res2->_base;
  while (!(l1->isClauseMarker()) && !(l2->isClauseMarker())) {
    if (l1->getValue() < l2->getValue()) {
      *curr = *l1;
      l1 += 1;
    } else if (l1->getValue() > l2->getValue()) {
      *curr = *l2;
      l2 += 1;
    } else if (l1->getValue() == l2->getValue()) {
      *curr = *l1;
      l1 += 1;
      l2 += 1;       
    }
    if (curr->getValue() != varId) {
      // Make sure that the literal is not watched!!!
      curr->unwatch();
      curr += 1;
      _size += 1;
    } else {
      // Restore the end-of-clause marker
      curr->makeClauseMarker(1);
    }
  }
  while (!(l1->isClauseMarker())) {
    if (l1->getValue() != varId) {
      *curr = *l1;
      l1 += 1;
      // Make sure that the literal is not watched!!!
      curr->unwatch();
      curr += 1;
      _size += 1;
    }
  }
  while (!(l2->isClauseMarker())) {
    if (l2->getValue() != varId) {
      *curr = *l2;
      l2 += 1;
      // Make sure that the literal is not watched!!!
      curr->unwatch();
      curr += 1;
      _size += 1;
    }
  }

} // End of Clause::Clause(ClauseRef res1, ClauseRef res2, int varId)


/*****************************************************************************/
/*! clause constructor
 *
 *  \param res1   first resolvent.
 *  \param res2   second resolvent.
 *  \param varId  resolved variable.
 *  \param i2r    index-to-reference table for Variables
 *  \param hasUip will be set to true if the resultin clause contains a UIP
 */
/*****************************************************************************/
Clauses::Clauses(ClauseRef res1, ClauseRef res2, int varId, 
	       vector<VariableRef>& i2r, bool& hasUip)
{

  // This is a conflict-generated clause
  //if (res2->_size > 9) {
  // printf("Bef2 %d \n",(res2->_base+7)->getValue());
  // }

  _id = _size = 0;

  //if (res2->_size > 9) {
  //printf("Bef %d \n",(res2->_base+7)->getValue());
  //}
  //printf(" %d %d \n", res1->_size, res2->_size);
  // capacity allows two more elements for clause markers
  _base = (new Literal[res1->_size + res2->_size]) + 1;
  //if (res2->_size > 9) {
  //printf("Aft %d \n",(res2->_base+7)->getValue());
  //}

  LiteralRef curr = _base;

  // Sorted merge of literals

  LiteralRef l1 = res1->_base;
  LiteralRef l2 = res2->_base;
  //  LiteralRef tmp = l2;

  //while (!(l2->isClauseMarker())) {
  //cout << *l2 << " "<<endl;
  //l2 += 1;
  //}
  //l2 = tmp;


  // UIP handling
  // The a literal in the resulting clause is a UIP iff it is
  // the only one at the maximum decision level
  hasUip = false;
  unsigned int maxLevel = 0;


  while (!(l1->isClauseMarker()) && !(l2->isClauseMarker())) {
    //    printf("%d %d \n",l1->getValue(),l2->getValue());
    //cout << *l1 << " " << *l2 << endl;
    if (l1->getValue() < l2->getValue()) {
      *curr = *l1;
      l1 += 1;
    } else if (l1->getValue() > l2->getValue()) {
      *curr = *l2;
      l2 += 1;
    } else if (l1->getValue() == l2->getValue()) {
      *curr = *l1;
      l1 += 1;
      l2 += 1;       
    }
    if (curr->getValue() != varId) {
      // Make sure that the literal is not watched!!!
      curr->unwatch();
      // Check UIPs
      if (i2r[curr->getValue()]->_level > maxLevel) {
	maxLevel = i2r[curr->getValue()]->_level;
	hasUip = true;
      } else if (hasUip && (i2r[curr->getValue()]->_level == maxLevel)) {
	hasUip = false;
      }
      curr += 1;
      _size += 1;
    } else {
      // Restore the end-of-clause marker
      curr->makeClauseMarker(1);
    }
  }
  //Rim
  //(_base+_size)->makeClauseMarker(1);  
  //(res1->_base+(res1->_size))->makeClauseMarker(1);


  //  LiteralRef tmp = l1;

  //while (!(l1->isClauseMarker())) {
  //cout << *l1 << " "<<endl;
  //l1 += 1;
  //}
  //l1 = tmp;



  while (!(l1->isClauseMarker())) {
    if (l1->getValue() != varId) {
      *curr = *l1;
      l1 += 1;
      // Make sure that the literal is not watched!!!
      curr->unwatch();
      // Check UIPs
      if (i2r[curr->getValue()]->_level > maxLevel) {
	maxLevel = i2r[curr->getValue()]->_level;
	hasUip = true;
      } else if (hasUip && (i2r[curr->getValue()]->_level == maxLevel)) {
	hasUip = false;
      }
      curr += 1;
      _size += 1;
    }
  }
  //LiteralRef tmp = l2; 
  //while (!(tmp->isClauseMarker())) {
  //  printf("%d\n ",tmp->getValue());
  //  tmp += 1;
  //}
  //  (res2->_base+(res2->_size))->makeClauseMarker(1); 
  while (!(l2->isClauseMarker())) {
    //cout << *l2 <<endl;
    if (l2->getValue() != varId) {
      *curr = *l2;
      l2 += 1;
      // Make sure that the literal is not watched!!!
      curr->unwatch();
      // Check UIPs
      if (i2r[curr->getValue()]->_level > maxLevel) {
	maxLevel = i2r[curr->getValue()]->_level;
	hasUip = true;
      } else if (hasUip && (i2r[curr->getValue()]->_level == maxLevel)) {
	hasUip = false;
      }
      curr += 1;
      _size += 1;
    }
  }
  //curr=_base;
  //printf("CheckOnCM");
  //for(curr=_base;!(curr->isClauseMarker()); curr++) {
  //printf(" %d",(curr->isClauseMarker() ? 1 : 0));
    
  //} 
  //printf(" %d",(curr->isClauseMarker() ? 1 : 0));
  //printf("\n");

} // End of Clause::Clause(ClauseRef res1, ClauseRef res2, int varId)


inline bool CompareLiterals(const Literal & l1, 
			   const Literal & l2) 
{	
  if (l1.getValue() < l2.getValue()) {
    return true;
  } else {
    return false;
  }
}

/*****************************************************************************/
/*! clause constructor
 *
 *  \param res1   first resolvent.
 *  \param res2   second resolvent.
 *  \param varId  resolved variable.
 *  \param i2r    index-to-reference table for Variables
 *  \param hasUip will be set to true if the resultin clause contains a UIP
 */
/*****************************************************************************/
//Clauses::Clauses(vector<VariableRef>& searchSt)
//Clauses::Clauses(vector<VariableRef>& i2r, bool * assignments, int sizeReason)
Clauses::Clauses(int numAtoms, int * reason, int sizeReason)
{
  //if (searchSt[9]->_reason != 0) {
  //printf("%d ",((searchSt[9]->_reason->_base+10)->isClauseMarker() ? 1 : 0));
  //}

  _id = _size = 0; 
  _base = (new Literal[sizeReason + 2]) + 1;

  //printf("Ci sono 7\n");

  //LiteralRef l; 
  // vector<int> lits

  LiteralRef curr = _base;
  //LiteralRef tmp ; 
   
     
   // Bisogna metterle ordinate.
  for(size_t i = 0; i < numAtoms; i++) {

  //for(size_t i = 0; i < searchSt.size(); i++) {
    // Devo girare l'assegnamento!
    // In simo0.cpp
    //Literal l(searchSt[i]->getId(),((searchSt[i]->_value == Variable::TT)? false: true));
    // In simo1.cpp
    //Literal l(i+1,((assignments[i] == true) ? false : true ));
    
    // Ora non devo girarli? Mi arrivano gia girati?

     if (reason[i] == 0) {
       continue;
     }
     Literal l(i+1,((reason[i] == 1) ? true : false ));
     //printf(" %d",searchSt[i]->getId()); 
     *curr = l;
     //cout << " " << *curr;
     curr->unwatch();
     curr += 1;
     _size += 1;
   }
  //printf("\n");
   //To do
  //LiteralRef first = _base;
  //LiteralRef last = _base+_size;
  // Da controllare 
  //::stable_sort(_base,_base+_size,CompareLiterals) ;

//     int tmp;
//     //rintf("Ci sono 8\n");   
//     size_t i = 0;
//     for(LiteralRef curri = _base; i < searchSt.size()-1;i++,curri++) {
//       size_t j = i +1;
//       for (LiteralRef currj = curri + 1 ; 
//            j < searchSt.size() ; currj++,j++) {
//         //printf("%d %d\n",curri->getValue(),currj->getValue()); 
//         if (curri->getValue() > currj->getValue()) {
//    	 tmp= curri->getRealValue();
//    	 curri->setRealValue(currj->getRealValue());
//    	 currj->setRealValue(tmp);
//  	 //printf("Ci sono 8.1\n");   
//  		  //*tmp = *curri;

//  	 //printf("Ci sono 8.2\n");
//           //*curri = *currj;
//           //*currj = *tmp;      
//         }
//       }
//     }
      
   //}
   //}
   // printf("Ci sono 9\n");
   curr->makeClauseMarker(1);
   //(_base - 1)->makeClauseMarker(1);

   //printf(" ORD "); 
   //curr = _base;
   //for(curr = _base; !(curr->isClauseMarker()); curr++) {
   
   //cout << " " << *curr << " " << (curr->isClauseMarker() ? "1" : "0");
   
   // curr += 1;
   
   //}
   //printf("\n");
   //(_base + _size)->makeClauseMarker(1);
   //(_base - 1)->makeClauseMarker(1);


 
}

/*****************************************************************************/
/*! membership testing
 *
 *  \param varId  variable index to test membership of.
 */
/*****************************************************************************/
bool Clauses::HasMember(int varId)
{
  LiteralRef curr = _base;
  while (!(curr->isClauseMarker())) {
    if (curr->getValue() == varId) {
      return true;
    }
    curr += 1;
  }
  return false;
} // End of Clause::HasMember


/*****************************************************************************/
/*! unit clause testing
 *
 *  \param i2r index-to-reference table for Variables
 */
/*****************************************************************************/
bool Clauses::isUnit(vector<VariableRef>& i2r)
{
   bool isUnit = false;
  for (LiteralRef curr = _base; !(curr->isClauseMarker()); curr++)  {
    if (i2r[curr->getValue()]->_value == Variable::DC) {
      if (!isUnit) {
	isUnit = true;
      } else {
	return false;
      }
    }
  }
  return true;
} // End of Clause::isUnit


/*****************************************************************************/
/*! binary clause testing
 *
 *  \param i2r index-to-reference table for Variables
 */
/*****************************************************************************/
bool Clauses::isBinary(vector<VariableRef>& i2r)
{
  size_t numBin=0;
  for (LiteralRef curr = _base; !(curr->isClauseMarker()); curr++)  {
    if (i2r[curr->getValue()]->_value == Variable::DC) {
      numBin++;
    }
    if (i2r[curr->getValue()]->isSatisfying(curr->getSign())) {
      return false;
    }
  }
  if (numBin == 2) {
    return true;
  } else {
    return false;
  }
} // End of Clause::isBinary


/*****************************************************************************/
/*! add a literal to a clause
 *
 *  \param l the literal to be added
 */
/*****************************************************************************/
void Clauses::PushLiteral(const Literal &l) 
{
  *(_base + _size) = l;
  _size += 1;
  return;
}


/*****************************************************************************/
/*! close the clause (stop adding literals to it)
 */
/*****************************************************************************/
void Clauses::Close() 
{
  (_base + _size)->makeClauseMarker(_id);
  (_base - 1)->makeClauseMarker(_id);
}


void Clauses::PrintClause(vector<VariableRef>& i2r)
{
  LiteralRef curr;
  int openLits = 0;
  bool subsumed = false;
  for (curr = _base; !(curr->isClauseMarker()); curr++) {
    //printf("%d %d \n ",curr->getValue(),(curr->isClauseMarker() ? 1 :0));
    if (i2r[curr->getValue()]->_value == Variable::DC) {
      openLits += 1;
    } else if (i2r[curr->getValue()]->isSatisfying(curr->getSign())) {
      subsumed = true;
    }
  }
  if (subsumed) {
    cout << "[";
  } else {
    cout << " ";
  }
  cout << "<" << openLits << "> ";
   for (curr = _base; !(curr->isClauseMarker()); curr++) {
    cout << *curr << " ";
    if (i2r[curr->getValue()]->_value == Variable::DC) {
      openLits += 1;
    }
  }
  if (subsumed) {
    cout << "]";
  }

  //   for (curr = _base; !(curr->isClauseMarker()); curr++) {
  //cout << *curr << " ";
  //}
} // End of Clause::PrintClause

void Clauses::PrintClauseSimplified(vector<VariableRef>& i2r)
{
  LiteralRef curr;
  bool subsumed = false;
  for (curr = _base; !(curr->isClauseMarker()); curr++) {
    if (i2r[curr->getValue()]->isSatisfying(curr->getSign())) {
      subsumed = true;
      break;
    }
  }
  if (!subsumed) {
    cout << "id: " << _id << " ";
    for (curr = _base; !(curr->isClauseMarker()); curr++) {
      if (i2r[curr->getValue()]->_value == Variable::DC) {
	cout << (curr->getSign() ? "" : "-") << curr->getValue() << " ";
      }
    }
    cout << "0" << endl;
  }
} // End of Clause::PrintClauseSimplified

//literal.cpp, 3

/******************************************************************************
 * Standard and user-defined includes					   
 *****************************************************************************/
// #include "Literal.h"

/*****************************************************************************/
/*! output operator for class literal.
 *
 *  \param  outStream the output stream.
 *  \param  l         the literal to be displayed.
 *  \return           the resulting stream.
 *  \pre              none.
 *  \post             none.
 *  \sa               class Literal.
 */
/*****************************************************************************/
ostream& operator<< (ostream& outStream, const Literal& l) {
  if (l.readClauseMarker() > 0) {
    return outStream << "(" << l.getValue() << ")";
  } else {
    return outStream << ((l.getSign() == false) ? "-" : "")
		     << l.getValue()
		     << (l.isWatched() ? 
			 (l.readDirection() > 0 ? ">" : "<") :
			 "");
  }
}

// Parameters.cpp

// #include "Parameters.h"

void Parameters::ParseCmdLine(int argc, char * argv[])
{
  //int    i = 1;
  int    i = 0;
  while (i < argc) {
    if (strcmp(argv[i],"+heuristic") == 0) {
      if (strcmp(argv[i+1],"static") == 0) {
	heuristic = STATIC;
      } else if (strcmp(argv[i+1],"random") == 0) {
	heuristic = D_RANDOM;
      } else if (strcmp(argv[i+1],"unit") == 0) {
	heuristic = D_UNIT;
      } else if (strcmp(argv[i+1],"unit21") == 0) {
	heuristic = D_UNIT;
	auxiliaryHeur |= R_BSCORE_UTIE;
      } else if (strcmp(argv[i+1],"unit12") == 0) {
	heuristic = D_UNIT;
	auxiliaryHeur |= R_USCORE_BTIE;
      } else if (strcmp(argv[i+1],"periodic") == 0) {
	heuristic = D_PERIODIC;
	if (strcmp(argv[i+2],"chaff") == 0) {
	  periodicHeur = P_CHAFF;
	  baseUpdateCycle = atoi(argv[i+3]);
	  i += 2;
	} else if (strcmp(argv[i+2],"unit") == 0) {
	  periodicHeur = P_UNIT;
	  baseUpdateCycle = atoi(argv[i+3]);
	  i += 2;
	} else if (strcmp(argv[i+2],"unit21") == 0) {
	  periodicHeur = P_UNIT;
	  auxiliaryHeur |= R_BSCORE_UTIE;
	  baseUpdateCycle = atoi(argv[i+3]);
	  i += 2;
	} else if (strcmp(argv[i+2],"unit12") == 0) {
	  periodicHeur = P_UNIT;
	  auxiliaryHeur |= R_USCORE_BTIE;
	  baseUpdateCycle = atoi(argv[i+3]);
	  i += 2;
	} else if (strcmp(argv[i+2],"GMT01") == 0) {
	  periodicHeur = P_GMT01;
	  auxiliaryHeur |= R_USCORE_BTIE;
	  baseUpdateCycle = atoi(argv[i+3]);
	  switchThreshold = atof(argv[i+4]);
	  i += 3;
	} else if (strcmp(argv[i+2],"GMT02") == 0) {
	  periodicHeur = P_GMT02;
	  auxiliaryHeur |= R_USCORE_BTIE;
	  baseUpdateCycle = atoi(argv[i+3]);
	  switchThreshold = atof(argv[i+4]);
	  i += 3;
	} else if (strcmp(argv[i+2],"GMT03") == 0) {
	  periodicHeur = P_GMT03;
	  auxiliaryHeur |= R_USCORE_BTIE;
	  baseUpdateCycle = atoi(argv[i+3]);
	  switchThreshold = atof(argv[i+4]);
	  i += 3;
	}
      } else {
	printf("Unrecognized periodic heuristic %s\n",argv[i+2]);
      }
      i += 2;
    } else if (strcmp(argv[i],"+dilemma") == 0) {
      auxiliaryHeur |= R_DILEMMA;
      i += 1;
    } else if (strcmp(argv[i],"+size") == 0) {
      relevance = false;
      learnOrder = atoi(argv[i+1]);
      i += 2;
    } else if (strcmp(argv[i],"+relevance") == 0) {
      relevance = true;
      learnOrder = atoi(argv[i+1]);
      i += 2;
    } else if (strcmp(argv[i],"+seed") == 0) {
      seed = atoi(argv[i+1]);
      i+=2;
    } else if (strcmp(argv[i],"+noise") == 0) {
      baseRandomness = atoi(argv[i+1]);
      i+=2;
    } else if (strcmp(argv[i],"+restart") == 0) {
      allowRestart = true;
      nextRestartTime = atoi(argv[i+1]);
      restartBacktrackIncr = atoi(argv[i+2]);
      i+=3;
    } else if (strcmp(argv[i],"+norestart") == 0) {
      allowRestart = false;
      i += 1;
    } else if (strcmp(argv[i],"+timeout") == 0) {
      timeout = atoi(argv[i+1]);
      i+=2;
    } else {
      // Simply discard unrecognized parameters
      i += 1;
    }
  }
  return;
} // End of Params::ParseCmdLine


void Parameters::GiveHelp(char * argv[])
{
  printf("Usage: %s filename seed [options]\n", argv[0]);
  printf("filename and seed MUST be the first and second arguments!\n");
  printf("Options are:\n\n");
  printf("  +timeout   <seconds>   CPU time limit\n\n");
  printf("  +heuristic <heur> [<per> <n> <tr>]\n");
  printf("             heur = {Static, Random, Periodic}\n");
  printf("             static   : split on the first open variable\n");
  printf("             random   : choose a variable uniformly at random\n");
  printf("             unit     : simple unit-based heuristic\n");
  printf("             unit21   : 2ary cl. scoring, 1ary cl. tie breaking\n");
  printf("             unit12   : 1ary cl. scoring, 2ary cl. tie breaking\n");
  printf("             periodic : periodic heuristic\n");
  printf("                        per {chaff, unit, unit21, unit12, GMT01\n");
  printf("                             GMT02, GMT03}\n");
  printf("                        n   is the update cycle\n");
  printf("                        tr  ONLY GMT0i needs a float 0 < tr < 1\n");
  printf("  +dilemma   apply dilemma rule\n\n");
  printf("  +size <n>        size learning with order n\n"); 
  printf("  +relevance <n>   relevance learning with order n\n\n"); 
  printf("  +noise <n>       from 0 to varnum (the highest the noisyest)\n");
  printf("  +restart <t> <n> enable restart\n");
  printf("                   <t> time between restarts (after the 1st one)\n");
  printf("                   <n> number of backtracks before restarting\n\n");
  printf("  +norestart       disable restart\n");
  return;
} // End of Params::GiveHelp

void Parameters::OutputDimacs()
{
  switch (heuristic) {
  case STATIC :
    printf("c Heuristic is STATIC.\n");
    break;
  case D_RANDOM :
    printf("c Heuristic is RANDOM.\n");
    break;
  case D_UNIT :
    printf("c Heuristic is UNIT ");
    if ((auxiliaryHeur & R_BSCORE_UTIE) != 0) {
      printf("(2 clauses score, 1 clauses tie break).\n");
    } else if ((auxiliaryHeur & R_USCORE_BTIE) != 0) {
      printf("(1 clauses score, 2 clauses tie break).\n");
    } else {
      printf("(1 clauses score, 1 clauses tie break).\n");
    }
    break;
  case D_PERIODIC :
    printf("c Heuristic is PERIODIC ");
    switch (periodicHeur) {
    case P_CHAFF :
      printf("(chaff, periodicity %d).\n", baseUpdateCycle);
      break;
    case P_UNIT :
      printf("(unit, periodicity %d ", baseUpdateCycle);
      if ((auxiliaryHeur & R_BSCORE_UTIE) != 0) {
	printf("2 clauses score, 1 clauses tie break).\n");
      } else if ((auxiliaryHeur & R_USCORE_BTIE) != 0) {
	printf("1 clauses score, 2 clauses tie break).\n");
      } else {
	printf("1 clauses score, 1 clauses tie break).\n");
      }
      break;
    case P_GMT01 :
      printf("(GMT01, periodicity %d, threshold %.2f ", 
	     baseUpdateCycle, switchThreshold);
      if ((auxiliaryHeur & R_BSCORE_UTIE) != 0) {
	printf("unit21).\n");
      } else if ((auxiliaryHeur & R_USCORE_BTIE) != 0) {
	printf("unit12).\n");
      } else {
	printf("unit).\n");
      } 
      break;
    case P_GMT02 :
      printf("(GMT02, periodicity %d, threshold %.2f ", 
	     baseUpdateCycle, switchThreshold);
      if ((auxiliaryHeur & R_BSCORE_UTIE) != 0) {
	printf("unit21).\n");
      } else if ((auxiliaryHeur & R_USCORE_BTIE) != 0) {
	printf("unit12).\n");
      } else {
	printf("unit).\n");
      } 
      break;
    case P_GMT03 :
      printf("(GMT03, periodicity %d, threshold %.2f ", 
	     baseUpdateCycle, switchThreshold);
      if ((auxiliaryHeur & R_BSCORE_UTIE) != 0) {
	printf("unit21).\n");
      } else if ((auxiliaryHeur & R_USCORE_BTIE) != 0) {
	printf("unit12).\n");
      } else {
	printf("unit).\n");
      } 
      break;
    }
    break;
  }
  printf("c Dilemma is %s.\n", 
	 ((auxiliaryHeur & R_DILEMMA) != 0 ? "enabled" : "disabled"));
  printf("c Forgetting of clauses is %s.\n", 
	 (relevance ? "enabled" : "disabled"));
  printf("c Random seed is %d.\n", seed);
  printf("c Noise is %d.\n", baseRandomness);
  printf("c Restart is %s ", (allowRestart ? "enabled" : "disabled"));
  if (allowRestart) {
    printf("(first restart after %d BTs, increment %d BTs).\n",
	   restartBacktrackIncr, restartBacktrackIncrIncr);
  } else {
    printf(".\n");
  }
  return;
}
  
// TimerSimo.cpp

// #include "TimerSimo.h"

#ifdef _WIN32	// marcy
#include <ctime>
float TimerSimo::Epoch()
{	return (ru=((double)clock() / CLOCKS_PER_SEC));
};


void TimerSimo::Start() {
  ru1=Epoch();
};


float TimerSimo::Elapsed() { 
  static float t;
  t=Epoch()-ru1;
  return t; 
}; 


void  TimerSimo::SetTimeout(int seconds, void(*handler)(int))  { 
fprintf(stderr,"WARNING: SetTimeout NOT SUPPORTED UNDER WINDOWS!\n");
}; 

#else
float TimerSimo::Epoch() {
  getrusage(RUSAGE_SELF, &ru);
  return (ru.ru_utime.tv_sec + ru.ru_utime.tv_usec/1.0e6+
	  ru.ru_stime.tv_sec + ru.ru_stime.tv_usec/1.0e6);
};


void TimerSimo::Start() {
  getrusage(RUSAGE_SELF,&ru1);
};


float TimerSimo::Elapsed() { 
  static float t; 
  getrusage(RUSAGE_SELF,&ru2); 
  t=ru2.ru_utime.tv_usec/1.0e6-ru1.ru_utime.tv_usec/1.0e6; 
  t+=ru2.ru_utime.tv_sec-ru1.ru_utime.tv_sec; 
  return t; 
}; 


void  TimerSimo::SetTimeout(int seconds, void(*handler)(int))  { 
  getrlimit(RLIMIT_CPU, &r); 
  r.rlim_cur = seconds; 
  setrlimit(RLIMIT_CPU, &r); 
  signal(SIGXCPU, handler);  
}; 
#endif

// Variable.cpp

/******************************************************************************
 * Standard and user-defined includes					   
 *****************************************************************************/
// #include "Variable.h"

/*****************************************************************************/
/*! default constructor
 *
 *  \param  none
 */
/*****************************************************************************/
Variable::Variable()
{
  _level = _mode = _id = 0;
  _value = DC;

#ifndef CHRONO_BACKTRACK
  _reason = 0;
#endif

  return;
} // End of Variable::Variable()


/*****************************************************************************/
/*! constructor
 *
 *  \param  id variable identifier
 */
/*****************************************************************************/
Variable::Variable(int id)
{
  _level = _mode = 0;
  _value = DC;
  _id = id;
  _posWatched.reserve(INIT_WATCHED_SIZE);
  _negWatched.reserve(INIT_WATCHED_SIZE);
#ifndef CHRONO_BACKTRACK
  _reason = 0;
#endif

} // End of Variable::Variable(int id)

// Statistics.cpp

// #include "Statistics.h"

Statistics::Statistics() 
{
  int i;
  for (i = 0; i < MAX_STATS; i++) {
    counting[i] = 0;
  }
  counting[LEARN_MIN] = 1000000;
  for (i = 0; i < MAX_TIMERS; i++) {
    timing[i] = 0.0;
  }
  return;
} // End of Statistics::Statistics() 

// solver.cpp

// #include "Solver.h"
// #include "ChooseVariable.h"


#define BUFDIM  5000 // For parsing (line size)


///////////////////////////////////////////////////////////////////////////////
//
// CLASS Solver PUBLIC METHODS
//
///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// Plain constructor
///////////////////////////////////////////////////////////////////////////////
Solver::Solver(int varNum, int clNum)
{

  _varNum = varNum;
  _clNum = clNum;
  
  _staticInitSolver();

} // End of Solver::Solver(int varNum, int clNum)


///////////////////////////////////////////////////////////////////////////////
// DIMACS file constructor
///////////////////////////////////////////////////////////////////////////////
Solver::Solver(FILE * inFile, bool erase)
{
  char  buffer[BUFDIM];
  int   varNum, clNum;
  int   lit, readCl, check;
  
  _timer.Start();

  // Check if the input file is OK.
  if (fgets(buffer, BUFDIM, inFile) == 0) {
    return;
  }

  // Scan the input file searching for a line that starts with 'p'. 
  while (buffer[0] != 'p') {
    if (fgets(buffer, BUFDIM, inFile) == 0) {
      // If there is no such line, this is not a DIMACS problem.
      return;
    }
  }
  
  // Check if the problem is a cnf. 
  if (sscanf(buffer, "p cnf %d %d", &varNum, &clNum) == 0) {
    return;
  }
    
  // Initialize the solver module. 
  _varNum = varNum;
  _clNum = clNum;
  _staticInitSolver();

  // Allocate the array for checking redundancies and  tautologies. 
//    vector <int> propCheck;
//    propCheck.resize(varNum + 1, 0);

  // Allocate the array for checking redundancies and  tautologies. 
  vector <int> propCheckPos;
  propCheckPos.resize(varNum + 1, 0);

  // We ll use propCheckPos for _erase = false and _erase = true

  vector <int> propCheckNeg;
  propCheckNeg.resize(varNum + 1, 0);
  

  // Allocate the array for literals. 
  vector <int> lits;
  lits.reserve(INIT_CLAUSE_SIZE);
   
  readCl = 0;


  while (!feof(inFile) && readCl < clNum) {
            
    // Read the clause. 
    while (fscanf(inFile, "%d", &lit) && (lit != 0)) {
  
      if (erase) {

        // A tautological clause can be eliminated
        check = lit * propCheckPos[abs(lit)];
  
        if (check == 0) {
          // First occurrence of the literal in this clause.
          lits.push_back(lit);            
          propCheckPos[abs(lit)] = (lit > 0 ? 1 : -1); 
        } else if (check < 0) {
          // This is a tautology: reset the flags. 
          for (size_t i = 0; i < lits.size(); i++) {
            propCheckPos[abs(lits[i])] = 0;
          }
          lits.resize(0);
          // Go to the end of the clause. 
          while (lit != 0) {
            fscanf(inFile,"%d",&lit);
          }
        }
      } else {

        // A tautological clause can not be eliminated      
        (lit > 0 ? (check = lit * propCheckNeg[abs(lit)]) : (check = lit * propCheckPos[abs(lit)]));

        if (check <= 0) {
          // First occurrence of the literal in this clause.
          lits.push_back(lit);            
          (lit > 0 ? (propCheckNeg[abs(lit)] = 1) : (propCheckPos[abs(lit)] = -1)); 
        }
      }
      
      // We do not erase tautologies

    } // fscanf(inFile,"%d",&lit) && (lit!=0) 
   
    ++readCl;

    if (lits.size() > 0) {
      // If the clause is not emtpy, reset the flags and store it. 
      for (size_t i = 0; i < lits.size(); i++) {

	propCheckNeg[abs(lits[i])] = 0;
	propCheckPos[abs(lits[i])] = 0;
      }
      AddCheckedClause(lits);
      lits.resize(0);
    }
  
  } // !feof(inFile) && ..
  
  _stats.timing[PARSE_TIME] = _timer.Elapsed();

  

  return;

} // End of Solver::Solver(FILE * inFile)


///////////////////////////////////////////////////////////////////////////////
// Destructor
///////////////////////////////////////////////////////////////////////////////
Solver:: ~Solver()
{
  size_t i;
#ifndef CHRONO_BACKTRACK
  // Take care of "hanging" reasons
  for (i = 0; i < _searchStack.size(); i++) {
    // If it is a deduction, and the reason was not learned 
    // it has to be deleted 
    if ((_searchStack[i]->_mode == DE) && 
	(_searchStack[i]->_reason->_id == 0)) {
      delete(_searchStack[i]->_reason);
    }
  }
#endif
  // Wipe away clauses and variables
  for (i = 0; i < _variables.size(); i++) {
    delete(_variables[i]);
  }
  for (i = 0; i < _clauses.size(); i++) {
    delete(_clauses[i]);
  }
}


// Function object for comparing on absolute values
class AbsValueCmp {
public:
  int operator()(const int& i1, const int& i2) const {
    return (abs(i1) < abs(i2));
  }
};

///////////////////////////////////////////////////////////////////////////////
// Clause uploading
///////////////////////////////////////////////////////////////////////////////
void Solver::AddCheckedClause(vector<int> &lits)
{
  // Sort literals in ascending order of truth values
  sort(lits.begin(), lits.end(), AbsValueCmp());

  // Create a new (empty) clause and add it  
  ClauseRef cl = new Clauses(_clauses.size(), lits.size());
  _clauses.push_back(cl);

  // Copy the literals in the clause
  for (size_t i = 0; i < lits.size(); i++) {
    int j = abs(lits[i]);
    VariableRef var = _id2Ref[j];
    if (var == 0) {
      // Create a new variable and add it
      var = new Variable(j);
      _variables.push_back(var);
      chooseVariable_->onAddVariable(var);
      // Store the new association
      _id2Ref[j] = var;
    }
    Literal l(j, lits[i] > 0);
    cl->PushLiteral(l);
    chooseVariable_->onAddLiteral(l);
  }
  // Commit the clause
  cl->Close();
  
  // Set 1 or 2 watched literals
  for (int i = 0; i < (lits.size() > 1 ? 2 : 1); i++) {
    LiteralRef w = cl->_base + i;
    w->watch(-1);
    if (w->getSign()) {
      _id2Ref[w->getValue()]->_posWatched.push_back(w);
    } else {
      _id2Ref[w->getValue()]->_negWatched.push_back(w);
    }
  }
  // Push unit clauses into the unit stack
  if (lits.size() == 1) {
    _unitStack.push_back(make_pair(*(cl->_base), cl));
  } 

  return;

} // End of Solver::AddCheckedClause


///////////////////////////////////////////////////////////////////////////////
// Main search loop
///////////////////////////////////////////////////////////////////////////////
Result Solver::Solve()
{ 

  VariableRef var;
  Variable::Value value;
  int mode;
  //int stop = 0;
 
  //_enum = false;
  // Run-time initializations
  //_dynamicInitSolver();

  _timer.Start();

  // Assignments enumeration loop
  do {

    // Start the search for a single assignment: p == 0 means that the search
    // must end. 
    do {
      if (UnitPropagate()) { 
        if (FormulaIsEmpty()) {
  	  _stats.timing[SEARCH_TIME] = _timer.Elapsed();

          // return SAT;
          //PrintStatsDimacs(SAT);
          //PrintStatsCmodels();   
	  //#ifdef SHORT_OUT
          //PrintStats(SAT);
	  //#else
          //PrintStatsDimacsSAT);
	  //#endif
	  //#ifdef CMODELS_OUT
          //PrintStatsCmodels();
	  //#endif       
          //var = Backtrack(value,mode,true);
          _timer.Start();
         
          break;
        } 
     
        // Returns 0 when there are no more open variables
        var = (*chooseVariable_)(value, mode);

      } else {
        // Returns 0 when no more backtracking is possible
        var = Backtrack(value, mode,false);
      }

      if (var != 0) {
#ifdef TRACE
        LetPropHaveValue(var->_id, value);
#endif
        (void) ExtendProp(var, value, mode);
      }
      _stats.counting[CYCLES_NO]++;

   } while (var != 0);
    //_stats.timing[SEARCH_TIME] = _timer.Elapsed()
    //return (FormulaIsEmpty() ? SAT : UNSAT);
    //PrintStats(FormulaIsEmpty() ? SAT : UNSAT);
    //if (FormulaIsEmpty()) {
    //PrintStatsCmodels();      
    //}

    _timer.Start();
    if (!_stop) {
      var = Backtrack(value,mode,true); 

      if (var != 0) {
        /* If there are yet assignments to try. */
        (void) ExtendProp(var, value, mode);
      } //else {
        /*The enumeration must end. */
    }
  } while (!_stop);

    //Da fare solo se l'ultimo BT e' stato un enumeratore?
    // O non lo si mette proprio ( potrei perdere qualcosa?)
  return UNSAT;
 
} // End of Solver::Solve



///////////////////////////////////////////////////////////////////////////////
// Main search loop
///////////////////////////////////////////////////////////////////////////////
//  Solver::Result Solver::Solve()
//  {

//    VariableRef var;
//    Variable::Value value;
//    int mode;
//    //int stop = 0;
 
//    //_enum = false;
//    // Run-time initializations
//    _dynamicInitSolver();

//    _timer.Start();

//    // Assignments enumeration loop
//    //  do {

//      // Start the search for a single assignment: p == 0 means that the search
//      // must end. 
//      do {
//        if (UnitPropagate()) {
//          if (FormulaIsEmpty()) {
//  	  _stats.timing[SEARCH_TIME] = _timer.Elapsed();
//            // return SAT;
//            //PrintStatsDimacs(SAT);
//  #ifndef SHORT_OUT
//            PrintStatsDimacs(SAT);
//  #else
//            PrintStats(SAT);
//  #endif
//  #ifdef CMODELS_OUT
//            PrintStatsCmodels();
//  #endif       
//            var = Backtrack(value,mode,true);
//            _timer.Start();
         
//            //break;
//            continue;  
//          } else {
     
//            // Returns 0 when there are no more open variables
//            var = (*chooseVariable_)(value, mode);
//  	}

//        } else {
//          // Returns 0 when no more backtracking is possible
//          var = Backtrack(value, mode,false);
//        }

//        if (var != 0) {
//  #ifdef TRACE
//          LetPropHaveValue(var->_id, value);
//  #endif
//          (void) ExtendProp(var, value, mode);
//        }
//        _stats.counting[CYCLES_NO]++;

//      } while (var != 0);

//      //_stats.timing[SEARCH_TIME] = _timer.Elapsed();
//      //return (FormulaIsEmpty() ? SAT : UNSAT);
//      //PrintStats(FormulaIsEmpty() ? SAT : UNSAT);
//      //_timer.Start();

//      //var = Backtrack(value,mode,true); 

//      //if (var != 0) {
//        /* If there are yet assignments to try. */
//      //(void) ExtendProp(var, value, mode);
//      // } //else {
//        /*The enumeration must end. */


//      // } while (!_stop);

//    //Da fare solo se l'ultimo BT e' stato un enumeratore?
//    // O non lo si mette proprio ( potrei perdere qualcosa?)
    
//     return (FormulaIsEmpty() ? SAT : UNSAT);
 
//  } // End of Solver::Solve


///////////////////////////////////////////////////////////////////////////////
// Propagate values
///////////////////////////////////////////////////////////////////////////////
bool Solver::ExtendProp(const VariableRef var, 
			   const Variable::Value value, const int mode)
{
  LiteralRef w1;
  LiteralRef w2;
  LiteralRef cLit;
  int        direction, cl = 0;

  //assert(var->_value == Variable::DC);
#ifndef CHRONO_BACKTRACK
  //assert((var->_reason == 0) || 
  //     (var->_reason->isUnit(_id2Ref)));
#endif

  vector<LiteralRef>& w = (value == Variable::TT ? 
			   var->_negWatched : var->_posWatched);
  // Unit resolution on watched literals
  // Scanning is in reverse so removal can be done from the tail
  vector<LiteralRef>::reverse_iterator i = w.rbegin();
  for (; i != w.rend(); i++) {
    // In this way we can deal with clauses of size 1
    w1 = w2 = *i;
    direction = w1->readDirection();
    cLit = w1;
    while ((cLit->readClauseMarker() == 0) || 
	   (direction == w1->readDirection())) {
      cLit += direction;
      if (cLit->readClauseMarker() != 0) {
	// Reached a clause marker
	cl = cLit->readClauseMarker();
	if (direction == w1->readDirection()) {
	  // If only one direction is explored, go for the other
	  cLit = w1;
	  direction = -direction;
	}
      } else if (cLit->isWatched()) {
	// Get the second watched literal
	w2 = cLit;
      } else if (_id2Ref[cLit->getValue()]->isMatching(cLit->getSign())) {
	// The current literal is either DONT_CARE or a subsumer
	if (cLit->getSign()) {
	  _id2Ref[cLit->getValue()]->_posWatched.push_back(cLit);
	} else {
	  _id2Ref[cLit->getValue()]->_negWatched.push_back(cLit);
	}
	cLit->watch(direction);
	// Stop watching the literal that got us here
	w1->unwatch();
	*i = w.back();
	w.pop_back();
	// Stop scanning this clause
	break;
      }
    }
    if (cLit->readClauseMarker() != 0) {
      // We swept the clause in both directions without 
      // finding a subsumer or an unassigned literal
      if ((w1 == w2) || 
	  (!(_id2Ref[w2->getValue()]->isMatching(w2->getSign())))) {
	// An empty clause!
#ifdef TRACE
	ContradictionFoundOn(w1->getValue());
#endif
#ifndef CHRONO_BACKTRACK
        _conflictCl1 = _clauses[cl]; // _emptyClauses (should be an array)
        _conflictCl2 = var->_reason; // _conflictVarReason
        _conflictVar = var;          // _conflictVar
#endif
	return false;
      } else if (_id2Ref[w2->getValue()]->_value == Variable::DC) {
	// A unit clause!
	_unitStack.push_back(make_pair(*w2, _clauses[cl]));
      }
    }
  }

  // Assigning value, mode and pushing var into the search stack
  var->_value = value;
  var->_mode = mode;
  var->_level = _levelID;
  _searchStack.push_back(var);
  _openVarNum--;

  return true;

} // End of Solver::ExtendProp


///////////////////////////////////////////////////////////////////////////////
// Retract values
///////////////////////////////////////////////////////////////////////////////
void Solver::RetractProp(const VariableRef var)
{
  //assert(var->_value != Variable::DC);

  // Notify the heuristic about the retract 
  chooseVariable_->onRetractProp(var);

  // Clear value and (eventually) reason
  var->_value = Variable::DC;
  _openVarNum++;
#ifndef CHRONO_BACKTRACK
  // If it is a deduction and the reason was not learned it should be cleared
  if ((var->_mode == DE) && (var->_reason->_id == 0)) {
    delete(var->_reason);
    var->_reason = 0;
  }
#endif
  return;
} // End of Solver::RetractProp


///////////////////////////////////////////////////////////////////////////////
// "lean" ExtendProp
///////////////////////////////////////////////////////////////////////////////
bool Solver::leanExtendProp(vector<Implied>& auxStack, 
			    VariableRef var, Variable::Value value, int mode,
			    unsigned int& binCount)
{
  LiteralRef w1;
  LiteralRef w2;
  LiteralRef cLit;
  int        direction, cl = 0;
  bool       isBin; 
  
  //assert(var->getValue() == Variable::DC);
#ifndef CHRONO_BACKTRACK
  //assert((var->getReason() == 0) || 
  //	 (var->getReason()->isUnit(_id2Ref)));
#endif

  vector<LiteralRef>& w = 
    (value == Variable::TT ? var->_negWatched : var->_posWatched);
  vector<VariableRef>& id2Ref = _id2Ref;
  // Unit resolution on watched literals
  // Scanning is in reverse so removal can be done from the tail
  vector<LiteralRef>::reverse_iterator i = w.rbegin();
  for (; i != w.rend(); i++) {
    // In this way we can deal with clauses of size 1
    w1 = w2 = *i;
    direction = w1->readDirection();
    cLit = w1;
    isBin = false;
    while ((cLit->readClauseMarker() == 0) || 
	   (direction == w1->readDirection())) {
      cLit += direction;
      if (cLit->readClauseMarker() != 0) {
	// Reached a clause marker
	cl = cLit->readClauseMarker();
	if (direction == w1->readDirection()) {
	  // If only one direction is explored, go for the other
	  cLit = w1;
	  direction = -direction;
	}
      } else if (cLit->isWatched()) {
	// Get the second watched literal
	w2 = cLit;
      } else if (id2Ref[cLit->getValue()]->isMatching(cLit->getSign())) {
	// The current literal is either DONT_CARE or a subsumer
	// Check for binary clauses
	if (!isBin) {
	    if (cLit->getSign()) {
		id2Ref[cLit->getValue()]->_posWatched.push_back(cLit);
            } else {
		id2Ref[cLit->getValue()]->_negWatched.push_back(cLit);
	    }
	    cLit->watch(direction);
	    isBin = true;
	    w1->unwatch();
	    *i = w.back();
	    w.pop_back();
	} else {
          isBin = false;
          break;
	}
      }
    }
    if (isBin) {
      binCount += 1;
    } else {
      if (cLit->readClauseMarker() != 0) {
	// We swept the clause in both directions without 
	// finding a subsumer or an unassigned literal
	if ((w1 == w2) || 
	    (!(id2Ref[w2->getValue()]->isMatching(w2->getSign())))) {
	  // An empty clause!
#ifndef CHRONO_BACKTRACK
	  _conflictCl1 = _clauses[cl]; 
	  _conflictCl2 = var->getReason();
	  _conflictVar = var;          
#endif
	  return false;
	} else if (id2Ref[w2->getValue()]->getValue() == Variable::DC) {
	  // A unit clause!
	  //assert(_clauses[cl]->isBinary(_id2Ref));
	  _unitStack.push_back(make_pair(*w2, _clauses[cl]));
	}
      }
    }
  }

  // Assigning value, mode and pushing var into the auxiliary stack
  var->_value = value;
  var->_mode = mode;
  Literal l(var->_id, (var->_value == Variable::TT ? true : false));
#ifndef CHRONO_BACKTRACK
  auxStack.push_back(make_pair(l, var->getReason()));
#else
  auxStack.push_back(make_pair(l, _clauses[0]));
#endif

  return true;

} // End of ChooseVariable::leanExtendProp


///////////////////////////////////////////////////////////////////////////////
// "lean" RetractProp
///////////////////////////////////////////////////////////////////////////////
void Solver::leanRetractProp(const VariableRef var)
{
  //assert(var->getValue() != Variable::DC);
  // Clear value and (eventually) reason
  var->_value = Variable::DC;
  return;
} // End of ChooseVariable::leanRetractProp


///////////////////////////////////////////////////////////////////////////////
// Unit propagation
///////////////////////////////////////////////////////////////////////////////
bool Solver::UnitPropagate()
{

  if (_forceBT == true) {
    _forceBT = false;
    return false;
  }

  while (_unitStack.size() > 0) {
    // Extract literal and reason from the unit stack
    Implied imp = _unitStack.back();
    _unitStack.pop_back();
    VariableRef var = _id2Ref[imp.first.getValue()];
    if (var->_value == Variable::DC) {
#ifndef CHRONO_BACKTRACK
      var->_reason = imp.second;
#endif
      if (!ExtendProp(var, (imp.first.getSign() ? Variable::TT : Variable::FF), DE)) {
	return false;
      } else {
#ifdef TRACE
	PropHasValue(var->_id, (imp.first.getSign() ? Variable::TT : Variable::FF));
#endif
	_stats.counting[UNIT_NO]++;
      }
    }
  } // while (_unitStack.size() > 0)
  return true;
} // End of Solver::UnitPropagate


///////////////////////////////////////////////////////////////////////////////
// Backtracking
///////////////////////////////////////////////////////////////////////////////
#ifdef CHRONO_BACKTRACK

///////////////////////////////////////////////////////////////////////////////
// Chronological Backtracking
///////////////////////////////////////////////////////////////////////////////
VariableRef Solver::Backtrack(Variable::Value& value, int &mode)
{
  // No backtracking from level 0
  if (_levelID == 0) {
    return 0;
  } 

  // Unit and (possibly) dilemma stack are always flushed
  _unitStack.resize(0);
  if ((_params.auxiliaryHeur & R_DILEMMA) != 0) {
    _dilemmaStack.resize(0);
  }
  _stats.counting[BACKTRACK_NO]++;
  while (_searchStack.size() > 0) {
    VariableRef lastVar = _searchStack.back();
    _searchStack.pop_back();
    if (lastVar->_mode == CH) {
      // The variable is an open choice point 
      value = (lastVar->_value == Variable::TT ? Variable::FF : Variable::TT);
      mode = DE;
      // Now this is a deduction performed at the previous level
      _levelID -= 1;
      _stats.counting[FDA_NO]++;
#ifdef TRACE
      RetractingProp(lastVar->_id);
#endif 
      RetractProp(lastVar);
      return lastVar;
    } else {
#ifdef TRACE
      RetractingProp(lastVar->_id);
#endif 
      RetractProp(lastVar);
    }
  } // while (_searchStack.size() > 0)
  return 0;
} // End of Solver::BackTrack

#else
///////////////////////////////////////////////////////////////////////////////
// Non-chronological Backtracking
///////////////////////////////////////////////////////////////////////////////
VariableRef Solver::Backtrack(Variable::Value& value, int &mode,bool _enum)
{
  unsigned int localSkip = 0;

  // No backtracking from level 0
  if (_levelID == 0) {
    _stop = true;
    return 0;
  } 

  // Obtain a new working reason from the conflicting clauses
  bool isUip = false;
  bool oneUipFound = false;
  bool discardWr = false;
  ClauseRef oldReason = 0;
  ClauseRef workReason;

  //  if ( _id2Ref[2]->_reason != 0) {
  //(_id2Ref[2]->_reason)->PrintClause(_id2Ref);
  //}

  if (_enum == false) {
    workReason = 
      new Clauses(_conflictCl1, _conflictCl2, _conflictVar->_id, _id2Ref, isUip); 
  } else {
    //    workReason = new Clause(_searchStack);
    //workReason = new Clause(_searchStack);
    //printf("In Back\n");
    //workReason -> PrintClause(_id2Ref);
    //printf("\n");
  }  

  // An empty working reason means that the formula is unsatisfiable
  if (workReason->_size == 0) {
    _stop = true;
    return 0;
  }

  
#ifdef TRACE
  if ( _enum == false) {
    NewWRfrom(_conflictCl1, _conflictCl2);
  }
  Becomes(workReason);
#endif
    
  // Unit stack is always flushed
  // Heuristics are notified about the backtrack
  _unitStack.resize(0);
  chooseVariable_->onBacktrack();

  _stats.counting[BACKTRACK_NO]++;
  // Temporary learned clauses stack is flushed
  _latestLearned.resize(0);

  while (_searchStack.size() > 0) {
    VariableRef lastVar = _searchStack.back();
    //ClauseRef c = lastVar->_reason; 
    //printf("LastVar\n");
    //if (lastVar->_reason != 0) {
    // Becomes(lastVar->_reason);
    //}
//      if (lastVar->_reason != 0) {
//        ClauseRef c = lastVar->_reason;
//        c -> PrintClause(_id2Ref);
//      }
    _searchStack.pop_back();
    // Keep the working reason if it is the first UIP found
    if (!oneUipFound && isUip) {
      oneUipFound = true;
      _latestLearned.push_back(workReason);
      discardWr = false;
      if (lastVar->_mode != CH) {
	_stats.counting[UIP_NO] += 1;
      }
    }
    if (workReason->HasMember(lastVar->_id)) {
      if (lastVar->_mode == CH) {
        // The variable is an open choice point responsible for the conflict
        // Update decision level
        _levelID -= 1;
        //if (_levelID == -1) {
	//printf("ERRORE");
        //}

#ifdef TRACE
	RetractingProp(lastVar->_id);
#endif 
        RetractProp(lastVar);
        if (localSkip > _stats.counting[SKIP_MAX]) {
          _stats.counting[SKIP_MAX] = localSkip;
        }
	// Awlays learn the asserting clause (if it is not learned yet)
	if (_latestLearned.back() != workReason) {
	  _latestLearned.push_back(workReason);
	}
	// Set literal watching and check if there are learned unit clauses
	for (size_t i = 0; i < _latestLearned.size(); i++) {
	  ScanLearned(_latestLearned[i]);
	}
	// Propagate learned unit clauses (also the older ones that
        // should be propagated at the current level, if any)
	if (UnitPropagateLearned()) {
	  //assert(lastVar->_value != Variable::DC);
	  // lastVar was propagated by unit, get another one
	  return (*chooseVariable_)(value, mode);
	} else {
	  // Unit propagation failed, must backtrack
	  return Backtrack(value, mode,false);
	}
      } else {
	// if (workReason->_size > 9) {
	//  printf("Bef1 %d \n",(workReason->_base+7)->getValue());
	//}

        // The variable is a deduction responsible for the conflict
	oldReason = workReason;
	//printf("Pos1 %d \n",(oldReason ->_base+7)->getValue());
        //(workReason)->PrintClause(_id2Ref);
        //printf("Sizes %d %d",(lastVar->_reason)->_size,workReason->_size);
	//if (workReason->_size > 9) {
	//  printf("Aft1 %d \n",(workReason->_base+7)->getValue());
	//}
	workReason = 
	  new Clauses(lastVar->getReason(), workReason, 
		     lastVar->_id, _id2Ref, isUip);
	if (workReason->_size == 0) {
          _stop = true;
	  return 0;
	}
#ifdef TRACE
	NewWRfrom(lastVar->getReason(), oldReason);
	Becomes(workReason);
	RetractingProp(lastVar->_id);
#endif 
	if (discardWr) {
	  delete oldReason;
	} else {
	  discardWr = true;
	}
        RetractProp(lastVar);
      }
    } else {
      // The variabile is not responsible for the conflict
      if (lastVar->_mode == CH) {
	// Keep levels updated
	_levelID -= 1;
#ifdef TRACE
        Skipping(lastVar->_id);
#endif
        _stats.counting[SKIP_NO] += 1;
        localSkip += 1;
        // E' il posto giusto?
        _bjOccur = true;
      }
#ifdef TRACE
      RetractingProp(lastVar->_id);
#endif 
      RetractProp(lastVar);
    }
    
  } // while (_searchStack.size() > 0)

  _stop = true;
  return 0;

} // End of Solver::BackTrack

#endif


///////////////////////////////////////////////////////////////////////////////
// Restart
///////////////////////////////////////////////////////////////////////////////
void Solver::Restart(void) 
{
  if (_levelID > 1) {
    _stats.counting[RESTART_NO] += 1;
    chooseVariable_->beforeRestart();
    // Trace back to level 0 in the search stack
    VariableRef lastVar = _searchStack.back();
    while ((_searchStack.size() > 0) && (lastVar->_level > 0)) {
      RetractProp(lastVar);
      _searchStack.pop_back();
      lastVar = _searchStack.back();
    }
    _stats.counting[BACKTRACK_NO] += 1;   
    // Reset the level ID to level 0
    _levelID = 0;
#ifndef CHRONO_BACKTRACK
    // Propagate unit clauses depending on level 0
    bool res = UnitPropagateLearned();
    // There cannot be a contradictory clause at this point
    //assert(res == true);
#endif
    chooseVariable_->afterRestart();
  }
  return;
}

///////////////////////////////////////////////////////////////////////////////
// Getting the model (if any)
///////////////////////////////////////////////////////////////////////////////
void Solver::GetModel(vector<int> &modelAsInts)
{
  for (size_t i = 0; i < _variables.size(); i++) {
    // Simply get the original integer code
    if (_variables[i]->_value != Variable::DC) {
      modelAsInts.push_back((_variables[i]->_id) * 
			    (_variables[i]->_value));
    }
  }
} // End of Solver::GetModel


///////////////////////////////////////////////////////////////////////////////
// Getting the search path
///////////////////////////////////////////////////////////////////////////////
void Solver::GetChoices(vector<int> &modelAsInts)
{
  for (size_t i = 0; i < _variables.size(); i++) {
    // Simply get the original integer code
    if ((_variables[i]->_value != Variable::DC) && 
	(_variables[i]->_mode == CH)) {
      modelAsInts.push_back((_variables[i]->_id) * 
			    (_variables[i]->_value));
    }
  }
} // End of Solver::GetModel



///////////////////////////////////////////////////////////////////////////////
//
// CLASS Solver PRIVATE methods
//
///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// Static initializations (To be done before the formula is loaded)
///////////////////////////////////////////////////////////////////////////////
inline void Solver::_staticInitSolver()
{
  // Formula representation
  _variables.reserve(_varNum);
  _id2Ref.resize(_varNum + 1);
  // Be prepared to double the clause DB 
  _clauses.reserve(_clNum << 1);
  // Skip 0-th position in the clause index
  _clauses.push_back(0);

  // Search 
  _searchStack.reserve(_varNum);
  _unitStack.reserve(_clNum);
   
  // Backjumping and learning    
#ifndef CHRONO_BACKTRACK
  _conflictCl1 = _conflictCl2 = 0;
  _conflictVar = 0;
  // Reserve 25% of _clNum for latest learned clauses and deletion bin
  _latestLearned.reserve(_clNum);
  _toDelete.reserve(_clNum >> 2);
#endif

  // Bookkeeping 
  _openVarNum = 0;
  _levelID = 0;
  _bjOccur = true;
  _stop = false;
  _forceBT = false;

  // Variable selection
  chooseVariable_ = new ChooseVariable(this, _params);

} // End of Solver::_staticInitSolver()

///////////////////////////////////////////////////////////////////////////////
// Dynamic initializations (To be done before the search is started)
///////////////////////////////////////////////////////////////////////////////
inline void Solver::_dynamicInitSolver()
{
  // Adjust the number of variables and clauses to the *real* ones
  _openVarNum = _variables.size();
  _clNum = _clauses.size() - 1;

  // Seed the random generator
#ifdef _WIN32	// marcy
  srand(_params.seed);
#else
  srandom(_params.seed);
#endif

  // Set current parameters from start values
  _params.updateCycle = _params.baseUpdateCycle;
  _params.randomness = _params.baseRandomness;

  // Install the timeout and the handler
  //_timer.SetTimeout(_params.timeout, _handler);

  // ChooseVariable runtime initialization 
  chooseVariable_->doRuntimeInitialization();

  return;
} // End of Solver::_dynamicInitSolver()



///////////////////////////////////////////////////////////////////////////////
// Periodic function for restart
///////////////////////////////////////////////////////////////////////////////
void Solver::periodicCheckRestart()
{
  if (_params.allowRestart && 
      (_stats.counting[BACKTRACK_NO] > _params.nextRestartBacktrack)) {
    // Update the number of backtracks
    _params.nextRestartBacktrack += _params.restartBacktrackIncr;
    _params.restartBacktrackIncr += _params.restartBacktrackIncrIncr;
    // Compute the current search time 
    float current = _timer.Epoch();
    // Control if restart should occur
    if (current > _params.nextRestartTime) {
#ifdef TRACE
      printf("\n Restarting ... ");
#endif
      // Update the time for the next restart
      _params.nextRestartTime = current + _params.restartTimeIncr;
      _params.restartTimeIncr += _params.restartTimeIncrIncr;
      // Update parameters for heuristic
      _params.randomness = _params.restartRandomness;
      Restart();
    }
  } 
  return;
}

#ifndef CHRONO_BACKTRACK

///////////////////////////////////////////////////////////////////////////////
// Periodic function for forgetting clauses
///////////////////////////////////////////////////////////////////////////////
void Solver::periodicForgetClauses()
{
  if (_params.relevance && 
      (_stats.counting[BACKTRACK_NO] % _params.deletionCycle == 0)) {

    // Find out the clauses to be deleted and mark them
    for (size_t i = _clNum + 1; i < _clauses.size(); i++) {
      ClauseRef cl = _clauses[i];

      if (cl->_size >= _params.minLiteralsNum) {
	unsigned int subsLits = 0, openLits = 0;
	LiteralRef cLit = cl->_base;  
	while (!(cLit->isClauseMarker())) {
	  if (_id2Ref[cLit->getValue()]->_value == Variable::DC) {
	    openLits += 1;
	  } else if (_id2Ref[cLit->getValue()]->isSatisfying(cLit->getSign())) {
	    subsLits += 1;
	  }
	  if (openLits + subsLits > _params.learnOrder ) {

	    _toDelete.push_back(cl);
	    // Use clause markers to mark the literals as deleted
	    LiteralRef cLit2;
	    for (cLit2 = cLit; !(cLit2->isClauseMarker()); cLit2++) {
	      cLit2->makeClauseMarker(i);
	    }
	    for (cLit2 = cLit-1; !(cLit2->isClauseMarker()); cLit2--) {
	      cLit2->makeClauseMarker(i);
	    }
	    break;
	  }
	  cLit += 1;
	}
      }
    }

    // Now delete literals occurring in marked clauses from watched literals
    if (_toDelete.size() > 0) {
      for (size_t ii = 0; ii < _variables.size(); ii++) {
	VariableRef var = _variables[ii];
        vector<LiteralRef>::reverse_iterator i;
	for (i = var->_posWatched.rbegin(); 
	     i != var->_posWatched.rend(); i++) {
	  LiteralRef w = *i;
	  if (w->isClauseMarker()) {
	    *i = var->_posWatched.back();
	    var->_posWatched.pop_back();
	  }
	}
	for (i = var->_negWatched.rbegin(); 
	     i != var->_negWatched.rend(); i++) {
	  LiteralRef w = *i;
	  if (w->isClauseMarker()) {
	    *i = var->_negWatched.back();
	    var->_negWatched.pop_back();
	  }
	}
      }
      // Delete clauses
      while (_toDelete.size() > 0) {
	ClauseRef cl = _toDelete.back();
	LiteralRef cLit = cl->_base;  
	while (!(cLit->isClauseMarker())) {
          if (cLit->getSign()) {
            chooseVariable_->id2DataRef_[cLit->getValue()]->_posLitsCount -= 1;            
	  } else {
            chooseVariable_->id2DataRef_[cLit->getValue()]->_negLitsCount -= 1;
          }
        }
	unsigned int id = cl->_id;
	_toDelete.pop_back();
	// Replace cl with tail to keep clause DB compacted
	_clauses[id] = _clauses.back();
	_clauses[id]->_id = id;
	// Must updated in-clause markers as well!
	_clauses[id]->Close();
	_clauses.pop_back();
	_stats.counting[FORGET_NO] += 1;
	// Free memory
	delete cl;
      }
    }

  }

  return;

} // End of Solver::periodicForgetClauses()


///////////////////////////////////////////////////////////////////////////////
// Add a clause to the database
///////////////////////////////////////////////////////////////////////////////
inline void Solver::LearnClause(ClauseRef learnedCl) 
{ 
  // Add the clause and commit it
  _clauses.push_back(learnedCl);
  learnedCl->_id = _clauses.size() - 1;
  learnedCl->Close();

  LiteralRef curr ;
  //printf("Learn");
  //for(curr= learnedCl->_base; !(curr->isClauseMarker());curr++) {
  //cout << " " << *curr ;
  // }
  //cout << endl;
  
  if ((_params.heuristic == D_PERIODIC) &&
      ((_params.periodicHeur == P_CHAFF)||(_params.periodicHeur == P_GMT01)||
       (_params.periodicHeur == P_GMT02)||(_params.periodicHeur == P_GMT03))) {
    // Notify heuristic
    for (LiteralRef curr = learnedCl->_base; 
	 !(curr->isClauseMarker()); curr++) {
      chooseVariable_->onAddLiteral(*curr);
    }
  }

  // We cannot set 2 literal watching here, because
  // we still do not know how many literals will be open!
  // This is done afterwards in ScanLearned 

  // Statistics...
  _stats.counting[LEARN_NO]++;
  unsigned int totalLits = learnedCl->_size;
  _stats.counting[LEARN_AVE] += totalLits;
  if (totalLits > _stats.counting[LEARN_MAX]) {
    _stats.counting[LEARN_MAX] = totalLits;
  }
  if (totalLits < _stats.counting[LEARN_MIN]) {
    _stats.counting[LEARN_MIN] = totalLits;
  }
  
  return;
  
} // End of Solver::LearnClause

///////////////////////////////////////////////////////////////////////////////
// Scan a candidate clause for learning
///////////////////////////////////////////////////////////////////////////////
void Solver::ScanLearned(ClauseRef learnedCl)
{
  VarAtLevel varAtLevel;

  // Search for unit on learned and set watched literals
  LiteralRef w[2];
  LiteralRef maxCurr = 0;
  unsigned int maxLevel = 0;
  unsigned int openLiterals = 0;
  for (LiteralRef curr = learnedCl->_base; 
       !(curr->isClauseMarker()); curr++) {
    if (_id2Ref[curr->getValue()]->_value == Variable::DC) {
      // Record a possible unit on learned
      if (openLiterals == 0) {
	varAtLevel._var = _id2Ref[curr->getValue()];
	varAtLevel._sign = curr->getSign();
	varAtLevel._reason = learnedCl;
      }
      // Set literal watching
      if (openLiterals < 2) {
	w[openLiterals] = curr;
      }
      openLiterals += 1;
    } else if (_id2Ref[curr->getValue()]->_level >= maxLevel) {
      maxLevel = _id2Ref[curr->getValue()]->_level;
      maxCurr = curr;
    }
  }

  // Learn the clause
  LearnClause(learnedCl);
  if (openLiterals == 1) {
    // Unit on learned
    _unitAtLevel.insert(make_pair(maxLevel, varAtLevel));
    // Do not set the second watched literal if maxCurr is 0
    w[1] = maxCurr;
    //assert(w[0] != w[1]);
    for (int j = 0; j < (maxCurr != 0 ? 2 : 1); j++) {
      w[j]->watch(-1);
      if (w[j]->getSign()) {
	_id2Ref[w[j]->getValue()]->_posWatched.push_back(w[j]);
      } else {
	_id2Ref[w[j]->getValue()]->_negWatched.push_back(w[j]);
      }
    }
  } else {
    //assert(w[0] != w[1]);
    for (int j = 0; j < 2; j++) {
      w[j]->watch(-1);
      if (w[j]->getSign()) {
	_id2Ref[w[j]->getValue()]->_posWatched.push_back(w[j]);
      } else {
	_id2Ref[w[j]->getValue()]->_negWatched.push_back(w[j]);
      }
    }
  }

  return;
}

///////////////////////////////////////////////////////////////////////////////
// Propagate unit on learned clauses
///////////////////////////////////////////////////////////////////////////////
bool Solver::UnitPropagateLearned()
{
  map<int,VarAtLevel>::iterator pi;
  bool                          res = true;

  // Assign values to unit on learned
  for  (pi = _unitAtLevel.begin(); 
	(pi != _unitAtLevel.end()) && res; pi++) {
    if ((pi->second._var->_value == Variable::DC) && 
	(pi->first <= _levelID)) {
      // Record reason
      //printf("pi\n");
      //pi->second._reason->PrintClause(_id2Ref);
      pi->second._var->_reason = pi->second._reason;
      // Do propagation
      if (pi->second._sign == true) {
	res = ExtendProp(pi->second._var, Variable::TT, DE);
#ifdef TRACE
	PropHasValue(pi->second._var->_id, Variable::TT);
#endif
      } else {
	res = ExtendProp(pi->second._var, Variable::FF, DE);
#ifdef TRACE
	PropHasValue(pi->second._var->_id, Variable::FF);
#endif
      }
      _stats.counting[UNIT_NO]++;
    }
  }
  // Clear the unitAtLevel database from the assignments
  // that pertain to this level
  for  (pi = _unitAtLevel.begin(); pi != _unitAtLevel.end(); pi++) {
    if (pi->first >= _levelID) {
      _unitAtLevel.erase(pi);
    }
  }
  return (res && UnitPropagate());
}

#endif

// Solver_output.cpp

// #include "Solver.h"

void Solver::PrintStatsDimacs(Result result)
{
  // Output relevant parameters
  printf("c SIMO configuration:\n");
  _params.OutputDimacs();
  // Output relevant statistics
  printf("c SIMO statistics:\n");
  printf("c Search nodes               %10d\n", _stats.counting[CHOICE_NO]);
  printf("c Unit clauses               %10d\n", _stats.counting[UNIT_NO]);
  printf("c Failure driven assignments %10d\n", _stats.counting[FDA_NO]);
  printf("c Dilemma literals           %10d\n", _stats.counting[DILEMMA_NO]);
  printf("c Backtracks                 %10d\n", _stats.counting[BACKTRACK_NO]);
  printf("c Restarts                   %10d\n", _stats.counting[RESTART_NO]);
  printf("c Current depth              %10d\n", _levelID);
#ifndef CHRONO_BACKTRACK
  printf("c Skipped choices            %10d\n", _stats.counting[SKIP_NO]);
  printf("c Highest backjump           %10d\n", _stats.counting[SKIP_MAX]);
  printf("c Learned clauses            %10d\n", _stats.counting[LEARN_NO]);
  printf("c UIPs                       %10d\n", _stats.counting[UIP_NO]);
  printf("c Largest learned            %10d\n", _stats.counting[LEARN_MAX]);
  printf("c Smallest learned           %10d\n", _stats.counting[LEARN_MIN]);
  if (_stats.counting[LEARN_NO] != 0) {
    printf("c Average                    %10d\n", 
	   _stats.counting[LEARN_AVE] / _stats.counting[LEARN_NO]);
  }
  printf("c Forgotten clauses          %10d\n", _stats.counting[FORGET_NO]); 
#endif
  
  // Final result
  printf("s %s\n", ((result == UNKNOWN) ? "UNKNOWN" : 
		    ((result == SAT) ? "SATISFIABLE" : "UNSATISFIABLE")));
  // Print out the model (if any) putting 10 literals per line at most
  if (result == SAT) {
    size_t i;
    printf("v ");
    for (i = 0; i < _searchStack.size(); i++) {
      printf("%d ", _searchStack[i]->_value * (_searchStack[i]->_id));
      printf("%d ", ((_searchStack[i]->_mode == CH) ? 0 : 1));// CH 0 ,DE 1
      if ((i != 0) && (i % 10) == 0) {
	printf("\n"); printf("v ");
      }
    }
    if (((i - 1) % 10) != 0) {
      printf("\n"); 
    }
  }
  // Conclude report with search time
  if (result != UNKNOWN) {
    printf("c Done (Search time %.3f CPU seconds).\n", 
	   _stats.timing[SEARCH_TIME]);
  } else {
    printf("c Instance timed out.\n");
  }
  return;
} // End of SATsolver::PrintStatsDimacs()

void Solver::PrintStats(Result result)
{
  // Final result
  printf("%s", ((result == UNKNOWN) ? 
		"-1 " : ((result == SAT) ? "1 " : "0 ")));
  // Search time
  if (result != UNKNOWN) {
    printf("%.3f ", _stats.timing[SEARCH_TIME]);
  } else {
    printf("%.3f ", (float)_params.timeout);
  }
  // Some stats (tries, nodes, bactracks)
  printf("%d %d %d %d %d %d %d %d\n", 
	 (_stats.counting[UNIT_NO] + _stats.counting[CHOICE_NO] +
	 _stats.counting[FDA_NO] + _stats.counting[DILEMMA_NO]) +
         _stats.counting[STATIC_PURE_NO],
         _stats.counting[UNIT_NO],
	 _stats.counting[CHOICE_NO], _stats.counting[BACKTRACK_NO],
         _stats.counting[FDA_NO],_stats.counting[PER_CHAFF_NO],
         _stats.counting[PER_UNIT_NO],_stats.counting[SKIP_NO]);
  return;
} // End of Solver::PrintStats()

void Solver::PrintStatsCmodels(bool * assignments, int * modes)
{
  size_t i; 
  //  int outFormat[_varNum+1];
  int * outFormat;
  outFormat=(int*)malloc(sizeof(int)*(_varNum+1));
  if(outFormat==NULL){
	cerr<<"Could not allocate enough space"<<endl;
  }
  //assignments = new bool[_varNum];

  // VEDERE SE SI PUO USARE _id2Ref PER VELOCIZZARE

  for (size_t i = 0;  i <= _varNum; i++) {
    outFormat[i] = 2;
  }	
  //  printf("Stack %d\n",_searchStack.size());
  for (size_t i = 0; i < _searchStack.size(); i++) {
    outFormat[_searchStack[i]->_id] = 
    (_searchStack[i]->_value == Variable::TT ? 1 : 0);
    //    printf("%d ",_searchStack[i]->_value * _searchStack[i]->_id);
    //modes[(_searchStack[i]->_id)-1] = ( _searchStack[i]->_mode == CH ? i+1 : ((i+1) - 2 * (i+1)));  
    modes[(_searchStack[i]->_id)-1] = i+1;  
  }
  //  printf("\n");
  //  printf("%s","\"");
  //printf("%s","[");
  //cout << """ << "[" << endl
  for (i = 1; i <= _varNum; i++) {
    //printf("%s",(outFormat[i] == 2 ? "X" : (outFormat[i] == 1 ? "1" : "0")));
    assignments[i-1] = (outFormat[i] == 1 ? true : false);
    //  printf("%s",outFormat[i]);
  }
  //printf("%s%s","]","\"");
  //printf("\n");
  //for (size_t j = 0; j < _varNum ; j++) {
  //printf("%d ",modes[j]);
  //}
  //printf("\n");
  free(outFormat);
  return;
}

  
void Solver::PrintClauses() 
{
  for (size_t i = 1; i < _clauses.size(); i++) {
    ClauseRef c = _clauses[i];
    c -> PrintClause(_id2Ref);
    cout << endl;
  }
  return;
} // End of Solver::PrintClauses

void Solver::PrintSomeClauses(size_t begin, size_t end) 
{
  for (size_t i = begin; i < end; i++) {
    ClauseRef c = _clauses[i];
    c -> PrintClause(_id2Ref);
    cout << endl;
  }
  return;
} // End of Solver::PrintClauses

void Solver::PrintSimplified() 
{
  unsigned int maxOpen = 0;
  for (size_t i = 1; i < _variables.size(); i++) {
    if ((_variables[i]->_value == Variable::DC) && 
	(_variables[i]->_id > maxOpen)) {
      maxOpen = _variables[i]->_id;
    }
  } 
  printf("p cnf %d %d", maxOpen, _clauses.size());  
  for (size_t i = 1; i < _clauses.size(); i++) {
    ClauseRef c = _clauses[i];
    c -> PrintClauseSimplified(_id2Ref);
  }
  return;
} // End of Solver::PrintClauses

void Solver::PrintStack()
{
 
  static char * stackVal[2] = {"CH","DE"};
  
  for (size_t i = 0; i < _searchStack.size(); i++) {
    printf("%d%s ", 
           _searchStack[i] -> _value * (_searchStack[i] -> _id), 
           stackVal[_searchStack[i] -> _mode]);
  }
  printf("\n");

  return;

} // End of Solver::PrintStack. 

#ifndef CHRONO_BACKTRACK
void Solver::PrintUnitAtLevel()
{
  map<int,VarAtLevel>::iterator pi;

  for  (pi = _unitAtLevel.begin(); pi != _unitAtLevel.end(); pi++) {
    printf("Unit on learned %d at level %d\n",
	   (pi -> second._sign == true ? 
	    pi -> second._var -> _id : 
	    -1 * pi -> second._var -> _id),
	   pi -> first);
  }
  return;
}
#endif

// chooseVariable.cpp

// #include "ChooseVariable.h"
// #include "Solver.h"

// Magic Numbers
#define PWEIGHT       1024  // Weight for the product of scores (Unit)

///////////////////////////////////////////////////////////////////////////////
//
// CLASS VariableData PUBLIC METHODS
//
///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// Plain constructor
///////////////////////////////////////////////////////////////////////////////
VariableData::VariableData( void )
{
  _posLitsCount = _negLitsCount = 
    _oldPosLitsCount = _oldNegLitsCount = 0;
  _posScore = _negScore = _priority = 0;
}

///////////////////////////////////////////////////////////////////////////////
// Constructor with id
///////////////////////////////////////////////////////////////////////////////
VariableData::VariableData( VariableRef var )
{
  _var = var;
  _posLitsCount = _negLitsCount = 
    _oldPosLitsCount = _oldNegLitsCount = 0;
  _posScore = _negScore = _priority = 0;
}

///////////////////////////////////////////////////////////////////////////////
//
// CLASS ChooseVariable PUBLIC METHODS
//
///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// Plain constructor
///////////////////////////////////////////////////////////////////////////////
ChooseVariable::ChooseVariable( Solver* solver, 
				Parameters& params) :  params_(params)
{
  solver_ = solver;
  variablesData_.reserve(solver_->_varNum);
  id2DataRef_.reserve(solver_->_varNum + 1);
  // Must accomodate all the literals
  _dilemmaCheck.resize(2 * solver_->_varNum + 1);
  // Expect 1/8 of dilemmas at most
  _dilemmaStack.reserve(solver_->_varNum >> 3);
  // Expect 1/8 of propagations in a branch at most
  _auxStackTT.reserve(solver_->_varNum >> 3);
  _auxStackFF.reserve(solver->_varNum >> 3);
  _mustBacktrack = false;
} 

///////////////////////////////////////////////////////////////////////////////
// Dynamic initialization
///////////////////////////////////////////////////////////////////////////////
void ChooseVariable::doRuntimeInitialization( void )
{
  _varPriorityQueue.resize(variablesData_.size());
  for ( size_t i = 0 ; i < variablesData_.size(); i++ ) {
    // Reset the priority queue
    _varPriorityQueue[i] = pair<VariableData*, int>(variablesData_[i], 0);
    // Propagate initial pure literals 
    //      if (variablesData_[i]->_posLitsCount == 0) {
    //(void)solver_->ExtendProp(variablesData_[i]->_var, 
    //             	Variable::FF, Solver::CH);
//  //        //solver_->_levelID += 1;
//  #ifdef TRACE
//      printf("  [%d] has value %s at level %d as pure literal\n", variablesData_[i]->_var, "FF",solver_->_levelID);

//  #endif
  //    solver_->_stats.counting[STATIC_PURE_NO] += 1;
  //   } else if (variablesData_[i]->_negLitsCount == 0) {
  //  (void)solver_->ExtendProp(variablesData_[i]->_var, 
  //   		Variable::TT, Solver::CH);
//          //solver_->_levelID += 1;
//  #ifdef TRACE
//          printf("  [%d] has value %s at level %d as pure literal\n", variablesData_[i]->_var, "TT", solver_->_levelID);
//  #endif

    //  solver_->_stats.counting[STATIC_PURE_NO] += 1;
    //}
  }
} 

///////////////////////////////////////////////////////////////////////////////
// Main method
///////////////////////////////////////////////////////////////////////////////
VariableRef ChooseVariable::operator()( Variable::Value& value, int &mode )
{
  // Run periodic tasks
  if (params_.allowRestart) {
    solver_->periodicCheckRestart();
  }
  if (params_.heuristic == D_PERIODIC) {
    switch (params_.periodicHeur) {
    case P_CHAFF :
      periodicChaffOnlyUpdateStats(); break;
    case P_UNIT :
      periodicUnitUpdateStats(); break;
    case P_GMT01 :
      periodicGMT01UpdateStats(); break;
    case P_GMT02 :
      periodicGMT02UpdateStats(); break;
    case P_GMT03 :
      periodicGMT03UpdateStats(); break;
    default :
      periodicChaffOnlyUpdateStats(); break;
    }
  }
#ifndef CHRONO_BACKTRACK
  if (params_.relevance) {
    solver_->periodicForgetClauses();  
  }
#endif
  // Select and run the heuristic
  switch (params_.heuristic) {
  case STATIC  : 
    return StaticHeuristic(value, mode);
  case D_RANDOM  : 
    return RandomHeuristic(value, mode);
  case D_UNIT  : 
    return UnitHeuristic(value, mode);
  case D_PERIODIC  : 
    return PeriodicHeuristic(value, mode);
  default :
    //return RandomHeuristic(value, mode);
    return PeriodicHeuristic(value, mode);
  }
} // End of ChooseVariable::operator()(Variable::Value& value, int &mode)

///////////////////////////////////////////////////////////////////////////////
// Observing methods
///////////////////////////////////////////////////////////////////////////////
void ChooseVariable::onAddVariable(VariableRef var)
{
  VariableData* vd = new VariableData(var);
  variablesData_.push_back(vd);
  id2DataRef_[var->getId()] = vd;
}

void ChooseVariable::onAddLiteral(const Literal& l)
{
  if (l.getSign()) {
    id2DataRef_[l.getValue()]->_posLitsCount += 1;
  } else {
    id2DataRef_[l.getValue()]->_negLitsCount += 1;
  }
}

void ChooseVariable::onRetractProp(const VariableRef var) {
  if (id2DataRef_[var->getId()]->_priority < _maxPriorityIdx ) {
    _maxPriorityIdx = id2DataRef_[var->getId()]->_priority;
  }
}

void ChooseVariable::onBacktrack( void ) {
  if ((params_.auxiliaryHeur & R_DILEMMA) != 0) {
    _dilemmaStack.resize(0);
  }
}

void ChooseVariable::beforeRestart( void ) {
  if (params_.heuristic == D_PERIODIC) { 
    vector<VariableRef>& variables = solver_->_variables;
    switch (params_.periodicHeur) {
    case P_GMT01 : case P_GMT02 : case P_GMT03 :
      // Restore long periodicity
      params_.updateCycle = 256;
      // FALL THROUGH!!
    case  P_CHAFF :
      // Reset and update Chaff scores
      for (size_t i = 0; i < variablesData_.size(); ++i) {
	variablesData_[i]->_negScore = variablesData_[i]->_posScore = 0;
	variablesData_[i]->_oldPosLitsCount =
	  variablesData_[i]->_oldNegLitsCount = 0;
      }
      periodicChaffOnlyUpdateStats();
      break;
    default : 
      break;
    }
  }
}

void ChooseVariable::afterRestart( void ) {
  if ((params_.heuristic == D_PERIODIC) && 
      (params_.periodicHeur = P_UNIT)) {
    periodicUnitUpdateStats();
  }
}


///////////////////////////////////////////////////////////////////////////////
// Output methods
///////////////////////////////////////////////////////////////////////////////

void ChooseVariable::PrintPriorityQueue( void )
{
  for(vector<Priority>::iterator i = _varPriorityQueue.begin();
      i != _varPriorityQueue.end(); i++) {
    cout << i->first->_var->getId() << ":" << (*i).second << " ";
  }
  cout << endl;
}
  

///////////////////////////////////////////////////////////////////////////////
//
// CLASS ChooseVariable PRIVATE METHODS
//
///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
//
// StaticHeuristic 
// Chooses the first open variable.
//
///////////////////////////////////////////////////////////////////////////////
VariableRef ChooseVariable::StaticHeuristic(Variable::Value& value, int &mode)
{
  // Return the first open variable
  vector<VariableRef>& variables = solver_->_variables;
  for (size_t i = 0; i < variables.size(); i++) {
    if (variables[i]->getValue() == Variable::DC) {
      value = Variable::TT;
      mode = Solver::CH;
      solver_->_levelID += 1;
      solver_->_stats.counting[CHOICE_NO] += 1;
#ifndef CHRONO_BACKTRACK
      variables[i]->setReason(0);
#endif
      return variables[i];
    }
  }

  return 0;
} // End of Solver::StaticHeuristic


///////////////////////////////////////////////////////////////////////////////
//
// RandomHeuristic 
// Chooses an open variable uniformly at random.
//
///////////////////////////////////////////////////////////////////////////////
VariableRef ChooseVariable::RandomHeuristic(Variable::Value& value, int &mode)
{
#ifdef _WIN32	// marcy
  int rnd = rand() % solver_->_openVarNum + 1;
#else
  int rnd = random() % solver_->_openVarNum + 1;
#endif

  // Return an open variable at random
  vector<VariableRef>& variables = solver_->_variables;
  for (size_t i = 0; i < variables.size(); i++) {
    if (variables[i]->getValue() == Variable::DC) {
      rnd -= 1;
      if (rnd == 0) {
	// 50% chance of either positive or negative sign
#ifdef _WIN32	// marcy
	value = ((rand() & 1) == 0 ? Variable::TT : Variable::FF);
#else
	value = ((random() & 1) == 0 ? Variable::TT : Variable::FF);
#endif
	mode = Solver::CH;
	solver_->_levelID += 1;
	solver_->_stats.counting[CHOICE_NO] += 1;
#ifndef CHRONO_BACKTRACK
	variables[i]->setReason(0);
#endif
	return variables[i];
      }
    }
  }

  return 0;
} // End of ChooseVariable::RandomHeuristic


///////////////////////////////////////////////////////////////////////////////
//
// UnitHeuristic 
// Chooses the variable that maximizes the score:
// unitIfpos * unitIfneg * PWEIGHT + unitIfpos + unitIfneg + 1
//
// A reason is recorded for failed literals
//
///////////////////////////////////////////////////////////////////////////////
VariableRef ChooseVariable::UnitHeuristic(Variable::Value& value, int &mode)
{
  unsigned int posBin, negBin;
  unsigned int posUnit, negUnit;
  unsigned int score;
  unsigned int bestScore;
  VariableRef  var, bestVar;
 
  do {

    // Initializations
    bestScore = 0;
    bestVar = 0;

    // Examine open propositions.
    vector<VariableRef>& variables = solver_->_variables;
    for (size_t i = 0; i < variables.size(); i++) { 
      if ((variables[i]->getValue() == Variable::DC)) {
	var = variables[i];
        if ((var->getPosWatched().size() > 0) || 
	    (var->getNegWatched().size() > 0)) {
	  // Reset the auxiliary search stacks and (possibly) the dilemma stack
	  _auxStackTT.resize(0); _auxStackFF.resize(0);
	  if ((params_.auxiliaryHeur & R_DILEMMA) != 0) {
	    for (size_t j = 0; j < _dilemmaCheck.size(); j++) {
	      _dilemmaCheck[j] = false;
	    }
	    _dilemmaStack.resize(0);
	  }
	  //
	  // 1. Assign var to TT and do unit propagation 
	  //
	  posBin = 0; posUnit = 0;
#ifndef CHRONO_BACKTRACK
	  var->setReason(0);
#endif
	  (void) solver_->leanExtendProp(_auxStackTT, var, 
					 Variable::TT, Solver::CH, posBin);  
	  if (leanUnitPropagate(_auxStackTT, posBin, posUnit)) {
	    // On success, bactrack one-node (no CBJ and learning)
	    leanBacktrack(_auxStackTT, false);
#ifdef HEUR_TRACE
	    cout << "  Heur: " << var->getId() 
		 << " with value TT at level " << solver_->GetLevel()
		 << " has score " << posBin << ":" << posUnit << endl;
#endif      
	  } else {
	    // Let CBJ occur in the usual way
	    // leanBacktrack sets the reason of the failed literal as well
	    leanBacktrack(_auxStackTT, true);
#ifdef TRACE
	    PropIsFailed(var->getId(), Variable::FF, solver_->GetLevel());
#endif
	    // Assign the variable
	    (void) solver_->ExtendProp(var, Variable::FF, Solver::DE);  
	    if (!solver_->UnitPropagate()) {
	      return solver_->Backtrack(value, mode,false);
	    } else {
	      solver_->_stats.counting[FDA_NO] += 1;
	      continue;
	    }
	  }
	  //
	  // 2. Assign var to FF and do unit propagation 
	  //
	  negBin = 0; negUnit = 0;
#ifndef CHRONO_BACKTRACK
	  var->setReason(0);
#endif
	  (void) solver_->leanExtendProp(_auxStackFF, var, 
					 Variable::FF, Solver::CH, negBin);  
	  if (leanUnitPropagate(_auxStackFF, negBin, negUnit)) {
	    // On success, bactrack one-node
	    leanBacktrack(_auxStackFF, false);
#ifdef HEUR_TRACE
	    cout << "  Heur: " << var->getId() 
		 << " with value FF at level " << solver_->GetLevel()
		 << " has score " << negBin << ":" << negUnit << endl;
#endif      
	  } else {
	    // Let CBJ and (some) learning occur in the usual way
	    // leanBacktrack sets the reason of the failed literal as well
	    leanBacktrack(_auxStackFF, true);
#ifdef TRACE
	    PropIsFailed(var->getId(), Variable::TT, solver_->GetLevel());
#endif
	    // Assign the variable (Unit propagation CANNOT fail here!)
	    (void) solver_->ExtendProp(var, Variable::TT, Solver::DE);  
	    (void) solver_->UnitPropagate(); 
	    solver_->_stats.counting[FDA_NO] += 1;
	    continue;
	  }      
	  //
	  // 3. Check for dilemma and compute score
	  //
	  if ((params_.auxiliaryHeur & R_DILEMMA) != 0) {
	    // Propagate dilemma literals having the current var as hypothesis
	    bool res = DilemmaPropagate(var);
	    //assert(res == true);
	  }
	  if ((params_.auxiliaryHeur & R_BSCORE_UTIE) != 0) {  
	    // Use binary count for scoring and unit count for tie breaking
	    score = (posBin * negBin * PWEIGHT) + posUnit + negUnit + 1;  
	  } else if ((params_.auxiliaryHeur & R_USCORE_BTIE) != 0) {  
	    // Use unit count for scoring and binary count for tie breaking
	    score = (posUnit * negUnit * PWEIGHT) + posBin + negBin + 1;  
	  } else {
	    // Use unit count only
	    score = (posUnit * negUnit * PWEIGHT) + posUnit + negUnit + 1;  
	  }
	} else {
	  // If the variable is open but it does not have watched 
	  // occurrences then default its score to 1
	  score = 1;
	}
	if (score > bestScore) {
	  bestScore = score;
	  bestVar = var;
	}
      }
    } // End of for (int i = 0; i < _variables.size(); i++) 

  } while ((bestVar != 0) && (bestVar->getValue() != Variable::DC));
  // This is needed because we might have assigned our best variable
  // during a failed literal propagation: scoring must restart!
  
  if (bestVar != 0) {
    solver_->_levelID += 1;
    solver_->_stats.counting[CHOICE_NO] += 1;
    mode = Solver::CH;
    value = Variable::TT;
#ifndef CHRONO_BACKTRACK
    bestVar->setReason(0);
#endif
  }

  return bestVar;

} // End of ChooseVariable::UnitHeuristic


///////////////////////////////////////////////////////////////////////////////
//
// PeriodicHeuristic 
// Chooses the open variable with the highest priority (modulo some randomness)
//
///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// Variable-order predicate
///////////////////////////////////////////////////////////////////////////////
inline bool CompareVarStat(const pair<VariableData*, int> & v1, 
			   const pair<VariableData*, int> & v2) 
{	
  if (v1.second > v2.second) {
    return true;
  } else {
    return false;
  }
}

///////////////////////////////////////////////////////////////////////////////
// Selection of the variable to branch on
///////////////////////////////////////////////////////////////////////////////
VariableRef ChooseVariable::PeriodicHeuristic(Variable::Value& value, int &mode)
{

  //printf("Entro in periodic heuristic %d \n",solver_->_stats.counting[CHOICE_NO]);

  if (_mustBacktrack) {
    // Spotted a backtrack condition: reset flag and backtrack
    _mustBacktrack = false;
    return solver_->Backtrack(value, mode,false);
  } else if (solver_->_openVarNum == 0) {
    // No more open variables: the formula is SAT
    return 0;
  } else {
    // Select an open variable
    VariableRef var = 0;
    solver_->_stats.counting[CHOICE_NO] += 1;
    for (size_t i = _maxPriorityIdx; i < _varPriorityQueue.size(); i++) {
      var = _varPriorityQueue[i].first->_var;
      if ( var->getValue() == Variable::DC ) {
	// Move the maximum priority index
	_maxPriorityIdx = i;  
	if ( --(params_.randomness) < 
	     params_.baseRandomness ) {
	  params_.randomness = params_.baseRandomness;
	}
	int randomness = params_.randomness;
	// Make sure randomness is not greater than _openVarNum 
	if (randomness >= solver_->_openVarNum) {
	  randomness = solver_->_openVarNum - 1;
	}
	// Noisy choice of the best variable
#ifdef _WIN32	// marcy
	int skip = rand() % (1 + randomness);
#else
	int skip = random() % (1 + randomness);
#endif
	int idx = i;
	while ( skip > 0 ) {
	  ++idx;
	  if (_varPriorityQueue[idx].first->_var->getValue() == 
	      Variable::DC ) {
	    --skip;
	  }
	}
	VariableData* varData = _varPriorityQueue[idx].first;
        if (SATinstance->_heurfalse) {
          value = Variable::FF;
        } else {
	  value = (varData->_posScore > varData->_negScore ? 
		   Variable::TT : Variable::FF);
	}
	var = varData->_var;
	break;
      }
    }
    // Update level
    (solver_->_levelID) += 1;
    mode = Solver::CH;
#ifndef CHRONO_BACKTRACK
    if (var != 0) 
      var->setReason(0);
#endif
    return var;
  }
} // End of ChooseVariable::PeriodicHeuristic()

///////////////////////////////////////////////////////////////////////////////
// GMT01 periodic heuristic
///////////////////////////////////////////////////////////////////////////////
void ChooseVariable::periodicGMT01UpdateStats()
{
  static unsigned int lastBacktracks = 0;

  if ((solver_->_stats.counting[CHOICE_NO] % 
       params_.updateCycle) == 0) {

    // Compute threshold and variation in backtracks
    float choicheThreshold = 
      (float)params_.updateCycle * params_.switchThreshold;
    float deltaBacktracks = 
      (float)(solver_->_stats.counting[BACKTRACK_NO] - lastBacktracks);
    lastBacktracks = solver_->_stats.counting[BACKTRACK_NO];
    
    // Choose scoring method
    if (solver_->_bjOccur) {
      if (deltaBacktracks > choicheThreshold) {
      // Use base update cycle and fire periodicUnitUpdateStats
        solver_->_bjOccur = false;
        solver_->_stats.counting[PER_UNIT_NO] += 1;
        return periodicUnitUpdateStats();
      } else {

	// Switch to a large update cycle and fire periodicChaffUpdateStats
        solver_->_bjOccur = false;
        solver_->_stats.counting[PER_CHAFF_NO] += 1;
        return periodicChaffGMTUpdateStats();
      }
    } else {
      solver_->_bjOccur = false;
      solver_->_stats.counting[PER_UNIT_NO] += 1;
      return periodicUnitUpdateStats();
    }
  }

  return;

} // End of ChooseVariable::periodicGMT01UpdateStats()

///////////////////////////////////////////////////////////////////////////////
// GMT02 periodic heuristic
///////////////////////////////////////////////////////////////////////////////
void ChooseVariable::periodicGMT02UpdateStats()
{
  static unsigned int lastBacktracks = 0;

  if ((solver_->_stats.counting[CHOICE_NO] % 
       params_.updateCycle) == 0) {
    // Compute threshold and variation in backtracks
    float choicheThreshold = 
      (float)params_.updateCycle * params_.switchThreshold;
    float deltaBacktracks = 
      (float)(solver_->_stats.counting[BACKTRACK_NO] - lastBacktracks);
    lastBacktracks = solver_->_stats.counting[BACKTRACK_NO];
    
    // Choose scoring method
    if (deltaBacktracks > choicheThreshold) {
      // Use base update cycle and fire periodicUnitUpdateStats
      solver_->_stats.counting[PER_UNIT_NO] += 1;
      return periodicUnitUpdateStats();
    } else {
      // Switch to a large update cycle and fire periodicChaffUpdateStats
      if ( solver_->_bjOccur ) {
        //_params.updateCycle = 256;
        solver_->_stats.counting[PER_CHAFF_NO] += 1;
        return periodicChaffGMTUpdateStats();
      } else {
        solver_->_bjOccur = false;
        solver_->_stats.counting[PER_UNIT_NO] += 1;
        return periodicUnitUpdateStats();
      }
    }
  }

  return;

} // End of ChooseVariable::periodicGMT02UpdateStats()


///////////////////////////////////////////////////////////////////////////////
// GMT03 periodic heuristic
///////////////////////////////////////////////////////////////////////////////
void ChooseVariable::periodicGMT03UpdateStats()
{
  static unsigned int lastBacktracks = 0;

  if ((solver_->_stats.counting[CHOICE_NO] % 
       params_.updateCycle) == 0) {

    // Compute threshold and variation in backtracks
    float choicheThreshold = 
      (float)params_.updateCycle * 
      params_.switchThreshold;
    float deltaBacktracks = 
      (float)(solver_->_stats.counting[BACKTRACK_NO] - lastBacktracks);
    lastBacktracks = solver_->_stats.counting[BACKTRACK_NO];
    
    // Choose scoring method
    if (solver_->_bjOccur) {
      // Use base update cycle and fire periodicUnitUpdateStats
        solver_->_bjOccur = false;
        solver_->_stats.counting[PER_CHAFF_NO] += 1;
        return periodicChaffGMTUpdateStats();
    } else {
      // Switch to a large update cycle and fire periodicChaffUpdateStats
      if (deltaBacktracks > choicheThreshold) {
        solver_->_bjOccur = false;
        solver_->_stats.counting[PER_UNIT_NO] += 1;
        return periodicUnitUpdateStats();
      } else {
        solver_->_bjOccur = false;
        solver_->_stats.counting[PER_CHAFF_NO] += 1;
        return periodicChaffGMTUpdateStats();
      }
    }
  } 

  return;

} // End of ChooseVariable::periodicGMT03UpdateStats()

///////////////////////////////////////////////////////////////////////////////
// Periodic updating of scores (Unit-based)
///////////////////////////////////////////////////////////////////////////////
void ChooseVariable::periodicUnitUpdateStats()
{
  unsigned int posBin, negBin;
  unsigned int posUnit, negUnit;
  unsigned int score;
  VariableRef  var;

  if ((solver_->_stats.counting[CHOICE_NO] % 
       params_.updateCycle) == 0) {
    params_.updateCycle = params_.baseUpdateCycle;
    // Loop on open propositions.
    vector<VariableRef>& variables = solver_->_variables;
    for (size_t i = 0; i < variables.size(); i++) {
      var = variables[i];
      if (var->getValue() == Variable::DC) {
	if ((var->getPosWatched().size() > 0) || 
	    (var->getNegWatched().size() > 0)) {
	  // Reset the auxiliary search stacks and (possibly) the dilemma flags
	  _auxStackTT.resize(0); _auxStackFF.resize(0);
	  if ((params_.auxiliaryHeur & R_DILEMMA) != 0) {
	    for (size_t j = 0; j < _dilemmaCheck.size(); j++) {
	      _dilemmaCheck[j] = false;
	    }
	  }
	  // 
	  // 1. Assign var to TT and do unit propagation 
	  //
	  posBin = 0; posUnit = 0;
#ifndef CHRONO_BACKTRACK
	  var->setReason(0);
#endif
	  (void) solver_->leanExtendProp(_auxStackTT, var, 
					 Variable::TT, Solver::CH, posBin);
	  if (leanUnitPropagate(_auxStackTT, posBin, posUnit)) {
	    // On success, bactrack one-node (no CBJ and learning)
	    leanBacktrack(_auxStackTT, false);
#ifdef HEUR_TRACE
	    cout << "  Heur: " << var->getId() 
		 << " with value TT at level " << solver_->GetLevel() 
		 << " has score " << posBin << ":" << posUnit << endl;
#endif      
	  } else {
	    // Let CBJ occur in the usual way
	    // leanBacktrack sets the reason of the failed literal as well
	    leanBacktrack(_auxStackTT, true);
#ifdef TRACE
	    PropIsFailed(var->getId(), Variable::FF, solver_->GetLevel());
#endif
	    // Assign var to FF and do unit propagation 
	    (void) solver_->ExtendProp(var, Variable::FF, Solver::DE);  
	    if (!solver_->UnitPropagate()) {
	      // A contradiction: set backtrack flag and exit the loop
	      _mustBacktrack = true;              
	      break;
	    } else {
	      // The literal is failed, set the score to 0 and go on
	      _varPriorityQueue[i] = 
		pair<VariableData*, int>(id2DataRef_[var->getId()], 0);
	      solver_->_stats.counting[FDA_NO] += 1;
	      continue;
	    }
	  }
	  //
	  // 2. Assign var to FF and do unit propagation 
	  //
	  negBin = 0; negUnit = 0;
#ifndef CHRONO_BACKTRACK
	  var->setReason(0);
#endif
	  (void) solver_->leanExtendProp(_auxStackFF, var, 
					 Variable::FF, Solver::CH, negBin);
	  if (leanUnitPropagate(_auxStackFF, negBin, negUnit)) {
	    // On success, bactrack one-node
	    leanBacktrack(_auxStackFF, false);
#ifdef HEUR_TRACE
	    cout << "  Heur: " << var->getId()
		 << " with value FF at level " << GetLevel() 
		 << " has score " << negBin << ":" << negUnit << endl;
#endif      
	  } else {
	    // Let CBJ occur in the usual way
	    // leanBacktrack sets the reason of the failed literal as well
	    leanBacktrack(_auxStackFF, true);
#ifdef TRACE
	    PropIsFailed(var->getId(), Variable::TT, solver_->GetLevel());
#endif
	    // Assign the variable (Unit propagation CANNOT fail here!)
	    (void) solver_->ExtendProp(var, Variable::TT, Solver::DE);  
	    (void) solver_->UnitPropagate(); 
	    // The literal is failed, set the score to 0 and go on
	    _varPriorityQueue[i] = 
		pair<VariableData*, int>(id2DataRef_[var->getId()], 0);
	    solver_->_stats.counting[FDA_NO] += 1;
	    continue;
	  }
	  //
	  // 3. Check for dilemma and compute score
	  //
	  if ((params_.auxiliaryHeur & R_DILEMMA) != 0) {
	    // Propagate dilemma literals having the current var as hypothesis
	    bool res = DilemmaPropagate(var);
	    //assert(res == true);
	  }
	  if ((params_.auxiliaryHeur & R_BSCORE_UTIE) != 0) {  
	    // Use binary count for scoring and unit count for tie breaking
	    score = (posBin * negBin * PWEIGHT) + posUnit + negUnit + 1;  
	  } else if ((params_.auxiliaryHeur & R_USCORE_BTIE) != 0) {  
	    // Use unit count for scoring and binary count for tie breaking
	    score = (posUnit * negUnit * PWEIGHT) + posBin + negBin + 1;  
	  } else {
	    // Use unit count only
	    score = (posUnit * negUnit * PWEIGHT) + posUnit + negUnit + 1;  
	  }
	} else {
	  // If the variable is open but it does not have watched 
	  // occurrences then default its score to 1
	  score = 1;
	}
        // Update the PriorityQueue
	_varPriorityQueue[i] = 
		pair<VariableData*, int>(id2DataRef_[var->getId()], score);
      } else { 
	// If the variable is assigned move it to the bottom
        _varPriorityQueue[i] = 
	  pair<VariableData*, int>(id2DataRef_[var->getId()], score);
      }
    } // End of the loop on variables 

    if (!_mustBacktrack) {
      // Sort the priority queue
      ::stable_sort(_varPriorityQueue.begin(), 
		    _varPriorityQueue.end(), CompareVarStat); 
      
      // Update the priority record for each variable
      for (size_t i = 0; i < _varPriorityQueue.size(); i++) {
	_varPriorityQueue[i].first->_priority = i;
      }
      _maxPriorityIdx = 0;
      // Scoring was possible without troubles: restore standard update cycle
      params_.updateCycle = params_.baseUpdateCycle;
    } else {
      // Some troubles occurred: recalculate weights after backtracking
      params_.updateCycle = 1;
    }

  }

  return;
} // End of ChooseVariable::periodicUnitUpdateStats()


///////////////////////////////////////////////////////////////////////////////
// Periodic updating of scores (Chaff heuristic)
///////////////////////////////////////////////////////////////////////////////
void ChooseVariable::periodicChaffOnlyUpdateStats()
{

  //printf("Entro in periodic chaff %d \n",solver_->_stats.counting[CHOICE_NO]);

  if ((solver_->_stats.counting[CHOICE_NO] % 
       params_.updateCycle) == 0) {
    //printf("updateCyclein periodic chaff %d \n",solver_->_stats.counting[CHOICE_NO]);  
    // Sweep all the variables
    for (size_t i = 0; i < variablesData_.size(); i++) {
      VariableData* vd = variablesData_[i];
      // Update statistics
      vd->_posScore = 
	vd->_posScore / 2 + vd->_posLitsCount - vd->_oldPosLitsCount;
      vd->_negScore = 
	vd->_negScore / 2 + vd->_negLitsCount - vd->_oldNegLitsCount;
      // Save last count
      vd->_oldPosLitsCount = vd->_posLitsCount;
      vd->_oldNegLitsCount = vd->_negLitsCount;
      // Update priority queue using the highest score
      int bestScore = 
	(vd->_posScore > vd->_negScore ? vd->_posScore : vd->_negScore);
      _varPriorityQueue[i] = pair<VariableData*, int>(vd, bestScore);
    } 
    // Sort the scores
    ::stable_sort(_varPriorityQueue.begin(), 
		  _varPriorityQueue.end(), CompareVarStat); 
    // Update the priority record for each variable
    for (size_t i = 0; i < _varPriorityQueue.size(); i++) {
      _varPriorityQueue[i].first->_priority = i;
    }
    _maxPriorityIdx = 0;
  }
  return;
}

///////////////////////////////////////////////////////////////////////////////
// Periodic updating of scores (Chaff heuristic)
///////////////////////////////////////////////////////////////////////////////
void ChooseVariable::periodicChaffGMTUpdateStats()
{

  if ((solver_->_stats.counting[CHOICE_NO] % 
       params_.updateCycle) == 0) {
    params_.updateCycle = 256;
    // Sweep all the variables
    for (size_t i = 0; i < variablesData_.size(); i++) {
      VariableData* vd = variablesData_[i];
      // Update statistics
      vd->_posScore = 
	vd->_posScore / 2 + vd->_posLitsCount - vd->_oldPosLitsCount;
      vd->_negScore = 
	vd->_negScore / 2 + vd->_negLitsCount - vd->_oldNegLitsCount;
      // Save last count
      vd->_oldPosLitsCount = vd->_posLitsCount;
      vd->_oldNegLitsCount = vd->_negLitsCount;
      // Update priority queue using the highest score
      int bestScore = 
	(vd->_posScore > vd->_negScore ? vd->_posScore : vd->_negScore);
      _varPriorityQueue[i] = pair<VariableData*, int>(vd, bestScore);
    } 
    // Sort the scores
    ::stable_sort(_varPriorityQueue.begin(), 
		  _varPriorityQueue.end(), CompareVarStat); 
    // Update the priority record for each variable
    for (size_t i = 0; i < _varPriorityQueue.size(); i++) {
      _varPriorityQueue[i].first->_priority = i;
    }
    _maxPriorityIdx = 0;
  }
  return;
}

///////////////////////////////////////////////////////////////////////////////
// Dilemma propagation
///////////////////////////////////////////////////////////////////////////////
bool ChooseVariable::DilemmaPropagate(VariableRef hypVar) 
{
  // Scanning the Dilemma stack
  bool res = true;
  while (res && _dilemmaStack.size() > 0) {
    Implied imp = _dilemmaStack.back();
    _dilemmaStack.pop_back();
    VariableRef var = solver_->_id2Ref[imp.first.getValue()];
    if (var->getValue() == Variable::DC ) {
#ifndef CHRONO_BACKTRACK
      // Compute the reason for the dilemma
      ClauseRef wrTT = CreateDilemmaWr(_auxStackTT, imp.first);
      ClauseRef wrFF = CreateDilemmaWr(_auxStackFF, imp.first);
      ClauseRef wr = new Clauses(wrTT, wrFF, hypVar->getId());
      var->setReason(wr);
#endif
      // Assign the Dilemma and do unit propagation
      (void) solver_->ExtendProp(var, 
				 (imp.first.getSign() ? 
				  Variable::TT : Variable::FF), Solver::DE);
      solver_->_stats.counting[DILEMMA_NO] += 1;
      res = res || solver_->UnitPropagate();
    }
  }

  return res;
} // End of Solver::DilemmaPropagate(VariableRef hypVar) 


///////////////////////////////////////////////////////////////////////////////
// UnitPropagation
///////////////////////////////////////////////////////////////////////////////
bool ChooseVariable::leanUnitPropagate(vector<Implied>& auxStack, 
				  unsigned int& binCount, 
				  unsigned int& unitCount)
{
  while (solver_->_unitStack.size() > 0) {
    // Extract literal and reason from the unit stack
    Implied imp = solver_->_unitStack.back();
    solver_->_unitStack.pop_back();
    VariableRef var = solver_->_id2Ref[imp.first.getValue()];
    // if the variable is open
    if (var->getValue() == Variable::DC) {
      unitCount += 1;
      if ((params_.auxiliaryHeur & R_DILEMMA) != 0) {
	unsigned int idx = imp.first.computeIndex();
	if (_dilemmaCheck[idx]) {
	  // Dilemma found!
	  _dilemmaStack.push_back(imp);
	} else {
	  _dilemmaCheck[idx] = true;
	}
      }
#ifndef CHRONO_BACKTRACK
      var->setReason(imp.second);
#endif
      if (!solver_->leanExtendProp(auxStack, var, 
				   (imp.first.getSign() ? 
				    Variable::TT : Variable::FF),
				   Solver::DE, binCount)) {
	return false;
      }
    }
  } // while (_unitStack.size() > 0)
  return true;
} // End of ChooseVariable::leanUnitPropagate

///////////////////////////////////////////////////////////////////////////////
// Backtrack (does not compute a reason)
///////////////////////////////////////////////////////////////////////////////
void ChooseVariable::leanBtWithoutReason(vector<Implied>& auxStack)
{
  solver_->_unitStack.resize(0);
  for (vector<Implied>::reverse_iterator impPtr = auxStack.rbegin(); 
       impPtr != auxStack.rend(); impPtr++) {
    solver_->leanRetractProp(solver_->_id2Ref[impPtr->first.getValue()]);
  }
  return;
} // End of ChooseVariable::leanBtWithoutReason

#ifndef CHRONO_BACKTRACK
///////////////////////////////////////////////////////////////////////////////
// Backtrack (Computes a reason)
///////////////////////////////////////////////////////////////////////////////
void ChooseVariable::leanBtWithReason(vector<Implied>& auxStack)
{
  ClauseRef   oldReason, workReason;
  // Obtain a new working reason from the conflicting clauses
  pair<ClauseRef, ClauseRef> conflicts = solver_->getConflictClauses();
  workReason = new Clauses(conflicts.first, conflicts.second,
			  solver_->getConflictVariable()->getId()); 
  solver_->_unitStack.resize(0);
  // Reverse scan the auxiliary stack
  for (vector<Implied>::reverse_iterator impPtr = auxStack.rbegin(); 
       impPtr != auxStack.rend(); impPtr++) {
    VariableRef lastVar = solver_->_id2Ref[impPtr->first.getValue()];
    if (lastVar->getMode() == Solver::CH) {
      // The variable is the failed literal and is necessarily in the reason
      solver_->leanRetractProp(lastVar);
      lastVar->setReason(workReason);
      return;
    } else {
      if (workReason -> HasMember(lastVar->getId())) {
        // The variable is a deduction responsible for the conflict
        oldReason = workReason;
	workReason = 
	  new Clauses(lastVar->getReason(), oldReason, lastVar->getId());
	// Old reason was not learned and can be deleted
	delete(oldReason);
        solver_->leanRetractProp(lastVar);
      } else {
	// The variabile is not responsible for the conflict
	solver_->leanRetractProp(lastVar);
      }
    }
  } 

  return;

} // End of ChooseVariable::leanBtWithReason

///////////////////////////////////////////////////////////////////////////////
// Working reasons for dilemma literals
///////////////////////////////////////////////////////////////////////////////
ClauseRef ChooseVariable::CreateDilemmaWr(vector<Implied>& auxStack, 
				     Literal dilemma)
{
  ClauseRef oldReason, workReason;

  // Search for 'dilemma' in 'auxStack' 
  vector<Implied>::reverse_iterator impPtr = auxStack.rbegin(); 
  for (; impPtr != auxStack.rend() && !dilemma.isEqual(impPtr->first);
       impPtr++);
  workReason = impPtr->second;
  for (; impPtr != auxStack.rend(); impPtr++) {
    VariableRef lastVar = solver_->_id2Ref[impPtr->first.getValue()];
    if (workReason->HasMember(lastVar->getId())) {
      oldReason = workReason;
      workReason = 
	new Clauses(lastVar->getReason(), oldReason, lastVar->getId());
      if (oldReason->getId() == 0) {
	// Delete *temporary* reasons
	delete(oldReason);
      }
    }
  }

  // Return the reason for the dilemma
  return workReason;

} // End of ChooseVariable::CreateDilemmaWr

#endif


//  void loadFormula(int argc, char * argv[]) {

//    if (argc < 2) {
//      SATinstance = new Solver(0,0);
//      SATinstance->DisplayOptions(argv);
//      exit (RET_UNKNOWN);
//    }

//    // Load the instance from file and set the parameters
//    loadInstance(argc, argv);
//    if (SATinstance == 0) {
//      exit (RET_UNKNOWN);
//    }

//    SATinstance->_dynamicInitSolver();

//    return;
//  }

void loadFormula(char * nomefile, bool erase, bool heur_false, bool * ScopeOfNegAsFailure, int heur) {

  loadInstance(nomefile, erase);
  if (SATinstance == 0) {
    exit (RET_UNKNOWN);
  }

  SATinstance->_dynamicInitSolver();


  SATinstance->_heurfalse = heur_false;

  return;
}





void Reset() {

  //  printf(" CIAO2 ");
  delete(SATinstance);
  return;
}

//void Finisci() {
//  return SATinstance->Reset();
//} 

Result SingleSolve() { 
  
  //if ( SATinstance->Solve() == 1) {
  //  return 1;
  //} else {
  //return 0;
  //}
  VariableRef var;
  Variable::Value value;
  int mode;

  // Run-time initializations
  //_dynamicInitSolver();

  SATinstance->_timer.Start();

  if (SATinstance->_stop == true) {
    return UNSAT;
  }

  // Start the search
  do {
    if (SATinstance->UnitPropagate()) {
      if (SATinstance->FormulaIsEmpty()) {
	SATinstance->_stats.timing[SEARCH_TIME] = SATinstance->_timer.Elapsed();
        return SAT;
      }
      // Returns 0 when there are no more open variables
      var = (*SATinstance->chooseVariable_)(value, mode);
    } else {
      // Returns 0 when no more backtracking is possible
      var = SATinstance->Backtrack(value, mode, false);
    }

    if (var != 0) {
#ifdef TRACE
      LetPropHaveValue(var->_id, value);
#endif
      (void) SATinstance->ExtendProp(var, value, mode);
    }
    SATinstance->_stats.counting[CYCLES_NO]++;
  } while (var != 0);

  SATinstance->_stats.timing[SEARCH_TIME] = SATinstance->_timer.Elapsed();

  return (SATinstance->FormulaIsEmpty() ? SAT : UNSAT);

} // End of Solver::Solve


void BacktrackWithReason(bool hasLearning, int * reason, int * reason2, int sizeReason, int sizeReason2, bool sat) {

  unsigned int localSkip = 0;


  // No backtracking from level 0
  if (SATinstance->_levelID == 0) {
    SATinstance->_stop = true;
    return;
  } 

  // Obtain a new working reason from the conflicting clauses
  bool isUip = false;
  bool oneUipFound = false;
  bool discardWr = false;
  ClauseRef oldReason = 0;
  ClauseRef workReason, wr;

  SATinstance->_latestLearned.resize(0);

  //if (_enum == false) {
  //workReason = 
  //new Clause(_conflictCl1, _conflictCl2, _conflictVar->_id, _id2Ref, isUip); 
  //} else {
  // Was WR in simo0.cpp
  //workReason = new Clauses(SATinstance->_searchStack);
  // Was WR in simo0.h
  //workReason = new Clauses(SATinstance->_id2Ref, assignments, sizeReason);
 
    workReason = new Clauses(SATinstance->GetVariableNum(),reason, sizeReason);
    if (hasLearning) {
      SATinstance->_latestLearned.push_back(workReason);      
    }
    if (sat) {
      wr = new Clauses(SATinstance->GetVariableNum(),reason2, sizeReason2);
      SATinstance->_latestLearned.push_back(wr);
    }      

//    if ((sat) && (sizeReason2 < sizeReason)) {
//      workReason = new Clauses(SATinstance->GetVariableNum(),reason2, sizeReason2);
//      //    printf("WorkReasonSize %d\n", sizeReason2);
//    } else {
//      workReason = new Clauses(SATinstance->GetVariableNum(),reason, sizeReason);
//      //printf("WorkReasonSize %d\n", sizeReason);
//      //    printf("Reason %d\n",sizeReason);
//    }

//      if (hasLearning) {
//        SATinstance->_latestLearned.push_back(workReason);      
//        //Becomes(workReason);
//      }
//      if (sat) {
//        //    printf("Reason2 %d\n",sizeReason2);
//        if (sizeReason2 < sizeReason) {
//          wr = new Clauses(SATinstance->GetVariableNum(),reason, sizeReason);
//  	//printf("WrSize %d\n", sizeReason);
//        } else {
//          wr = new Clauses(SATinstance->GetVariableNum(),reason2, sizeReason2);
//  	//printf("WrSize %d\n", sizeReason2);
//        }
//        SATinstance->_latestLearned.push_back(wr);
//        //Becomes(wr);
//      }      
    //printf("In Back\n");
    //workReason -> PrintClause(_id2Ref);
    //printf("\n");
    //}  

  // An empty working reason means that the formula is unsatisfiable
  if (workReason->getSize() == 0) {
    SATinstance->_stop = true;
    return;
  }

  
#ifdef TRACE
  if ( _enum == false) {
    NewWRfrom(_conflictCl1, _conflictCl2);
  }
  Becomes(workReason);
#endif
    
  // Unit stack is always flushed
  // Heuristics are notified about the backtrack
  SATinstance->_unitStack.resize(0);
  SATinstance->chooseVariable_->onBacktrack();

  SATinstance->_stats.counting[BACKTRACK_NO]++;
  // Temporary learned clauses stack is flushed
  //SATinstance->_latestLearned.resize(0);

  while (SATinstance->_searchStack.size() > 0) {
    VariableRef lastVar = SATinstance->_searchStack.back();
    //ClauseRef c = lastVar->_reason; 
    //printf("LastVar\n");
    //if (lastVar->_reason != 0) {
    // Becomes(lastVar->_reason);
    //}
//      if (lastVar->_reason != 0) {
//        ClauseRef c = lastVar->_reason;
//        c -> PrintClause(_id2Ref);
//      }
    SATinstance->_searchStack.pop_back();
    // Keep the working reason if it is the first UIP found
    if (!oneUipFound && isUip) {
      oneUipFound = true;
      SATinstance->_latestLearned.push_back(workReason);
      discardWr = false;
      if (lastVar->getMode() != Solver::CH) {
	SATinstance->_stats.counting[UIP_NO] += 1;
      }
    }
    if (workReason->HasMember(lastVar->getId())) {
      if (lastVar->getMode() == Solver::CH) {
        // The variable is an open choice point responsible for the conflict
        // Update decision level
        SATinstance->_levelID -= 1;
        //if (_levelID == -1) {
	//printf("ERRORE");
        //}

#ifdef TRACE
	RetractingProp(lastVar->getId());
#endif 
        SATinstance->RetractProp(lastVar);
        if (localSkip > SATinstance->_stats.counting[SKIP_MAX]) {
          SATinstance->_stats.counting[SKIP_MAX] = localSkip;
        }
	// Awlays learn the asserting clause (if it is not learned yet)
	if (SATinstance->_latestLearned.back() != workReason) {
	  SATinstance->_latestLearned.push_back(workReason);
	}
	// Set literal watching and check if there are learned unit clauses
	for (size_t i = 0; i < SATinstance->_latestLearned.size(); i++) {
	  SATinstance->ScanLearned(SATinstance->_latestLearned[i]);
	}
	// Propagate learned unit clauses (also the older ones that
        // should be propagated at the current level, if any)
	if (SATinstance->UnitPropagateLearned()) {
	  //assert(lastVar->getValue() != Variable::DC);
	  // lastVar was propagated by unit, get another one
	  //return (*chooseVariable_)(value, mode);

          // Non ritorno nulla, andro a scegliere il nuovo letterale dalla
          // nuova solve, perche UP mi tornera SAT

          return;
	} else {
	  // Unit propagation failed, must backtrack
	  //return Backtrack(value, mode,false);
  
          // Devo tornare un flag e controllarlo in UP,
          // Se il flag e' attivo, UP mi deve far andare in Backtrack(false)
    
          SATinstance->_forceBT = true;
          return;

	}
      } else {
	// if (workReason->_size > 9) {
	//  printf("Bef1 %d \n",(workReason->_base+7)->getValue());
	//}

        // The variable is a deduction responsible for the conflict
	oldReason = workReason;
	//printf("Pos1 %d \n",(oldReason ->_base+7)->getValue());
        //(workReason)->PrintClause(_id2Ref);
        //printf("Sizes %d %d",(lastVar->_reason)->_size,workReason->_size);
	//if (workReason->_size > 9) {
	//  printf("Aft1 %d \n",(workReason->_base+7)->getValue());
	//}
	workReason = 
	  new Clauses(lastVar->getReason(), workReason, 
		     lastVar->getId(), SATinstance->_id2Ref, isUip);
	if (workReason->getSize() == 0) {
          SATinstance->_stop = true;
	  return;
	}
#ifdef TRACE
	NewWRfrom(lastVar->getReason(), oldReason);
	Becomes(workReason);
	RetractingProp(lastVar->getId());
#endif 
	if (discardWr) {
	  delete oldReason;
	} else {
	  discardWr = true;
	}
        SATinstance->RetractProp(lastVar);
      }
    } else {
      // The variabile is not responsible for the conflict
      if (lastVar->getMode() == Solver::CH) {
	// Keep levels updated
	SATinstance->_levelID -= 1;
#ifdef TRACE
        Skipping(lastVar->getId());
#endif
        SATinstance->_stats.counting[SKIP_NO] += 1;
        localSkip += 1;
        // E' il posto giusto?
        SATinstance->_bjOccur = true;
      }
#ifdef TRACE
      RetractingProp(lastVar->getId());
#endif 
      SATinstance->RetractProp(lastVar);
    }
    
  } // while (_searchStack.size() > 0)

  SATinstance->_stop = true;
  return;

} // End of Solver::BackTrack



void Print() {
  SATinstance->PrintClauses();
}

void PrintRes(bool * assignments, int * modes) { 

  //SATinstance->PrintStats(res); 
  //for (int i = 0; i < SATinstance->_varNum)
  SATinstance->PrintStatsCmodels(assignments, modes);   
}



// Main flow
//  int main(int argc, char * argv[]) 
//  {

//    loadFormula(argc,argv);
//    // Help requested?
//    //if (argc < 2) {
//    //SATinstance = new Solver(0,0);
//    //SATinstance->DisplayOptions(argv);
//    //exit (RET_UNKNOWN);
//    //}
//    //printf(" CIAO \n");
//    // Load the instance from file and set the parameters
//    //loadInstance(argc, argv);
//    //if (SATinstance == 0) {
//    //exit (RET_UNKNOWN);
//    //}

//    // Search for a single model and output results
//    Solver::Result res = SATinstance->Solve();
//    //#ifndef SHORT_OUT
//    //SATinstance->PrintStatsDimacs(res);
//    //#else
//    //SATinstance->PrintStats(res);
//    //#endif
  
//    // Wipe away the instance
//    delete(SATinstance);
//    Reset();

//    switch (res) {
//    case Solver::SAT : 
//      exit(RET_SATISFIABLE);
//    case Solver::UNSAT : 
//      exit(RET_UNSATISFIABLE);
//    default : 
//      exit(RET_UNKNOWN);
//    }

//  }

