/******************************************************************************
 * SIMO: Satisfiability Internal Module (Object oriented version)
 * Version 3.0
 * Copyright (C) 2000-2002 Enrico Giunchiglia, Marco Maratea, Armando Tacchella
 * 
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Library General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 * 
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 * 
 * For any questions regarding SIMO send e-mail to: sim@mrg.dist.unige.it
 * For more informations about SIMO see the homepage:
 * http://www.mrg.dist.unige.it/~sim
 * 
 * The LGPL is included in the SIMO distribution as the file LICENSE
 *****************************************************************************/

#ifndef SIMO_H
#define SIMO_H

/******************************************************************************
 * Standard and user-defined includes					   
 *****************************************************************************/

// STL stuff
//#include <stl.h>
#include <string>
#include <vector>
#include <utility>
#include <map>
#include <algorithm>
#include "defines.h"


// Vediamo
//#include "hash_map.h"
//#include "stack.h"
//#include "set.h"
//#include "algo.h"
//>
// Using std namespace for templates
using namespace std;

// Other standard stuff

#include <stdlib.h>
#include <time.h>
#include <assert.h>
#include <stdio.h>
#include <string.h>

/******************************************************************************
 * Defines
 * 
 * Default SIMO is BCP + heuristic + BJ + learning and no trace
 * Complile time switches are:
 * CHRONO_BACKTRACK Force chronological backtracking (no BJ, no learning)
 * TRACE            Enables code trace
 *****************************************************************************/

// Default (initial) sizes
#define INIT_CLAUSE_SIZE  (int)    4    // Clause size
#define INIT_WATCHED_SIZE (int)    4    // Watched literals size

// Rules for heuristics
#define R_DILEMMA      (unsigned int) 0x01  // Use dilemma rule
#define R_BSCORE_UTIE  (unsigned int) 0x02  // 2 cl. scoring, 1 cl. tie break
#define R_USCORE_BTIE  (unsigned int) 0x04  // 1 cl. scoring, 2 cl. tie break

/******************************************************************************
 * Prototypes
 *****************************************************************************/

// Core SAT solver
class Literal;
class Variable;
class Clauses;
class ChooseVariable;
class Solver;

// Utilities
class Parameters;
class Statistics;

//
//class SIMO;

/*****************************************************************************
 * Typedefs 
 ****************************************************************************/

typedef Literal  *               LiteralRef;   
typedef Variable *               VariableRef;  
typedef Clauses   *               ClauseRef;   
typedef pair<Literal, ClauseRef>       Implied;   // Literal and its reason

// Heuristics
typedef enum {
  STATIC,     // Static heuristic
  D_RANDOM,   // Random heuristic
  D_UNIT,     // Unit-based heuristic
  D_PERIODIC  // Periodic heuristic (see Heuristics.h)
} HeurType;

// Scores for periodic heuristics
typedef enum {
  P_CHAFF,        // Use Chaff scores 
  P_UNIT,         // Use Unit-based scores
  P_GMT01,        // Blend Chaff and Unit-based scores
  P_GMT02,        // Blend Chaff and Unit-based scores
  P_GMT03        // Blend Chaff and Unit-based scores
} PeriodType;

// Timing statistics
typedef enum {
  PARSE_TIME,
  SEARCH_TIME,
  MAX_TIMERS
} TimeStatType;

// Counting statistics
typedef enum {
  CHOICE_NO,        // Choices (i.e., calls to heuristic)
  UNIT_NO,          // Deductions on unit propagation
  FDA_NO,           // Deductions on failures
  DILEMMA_NO,       // Deductions on dilemma
  BACKTRACK_NO,     // Backtracks (i.e., calls to backtrack)
  CYCLES_NO,        // Cycles in the main loop
  SKIP_NO,          // Skipped choices with backjumping (total)
  SKIP_MAX,         // Highest backjump (number of choices)
  LEARN_NO,         // Learned clauses
  UIP_NO,           // Number of UIPs (excluding asserting clauses)
  FORGET_NO,        // Forgotten clauses
  LEARN_CLASH_NO,   // How many conflicts on learned
  LEARN_MAX,        // Biggest learned clause
  LEARN_MIN,        // Smallest learned clause    
  LEARN_AVE,        // Average size of learned clauses
  RESTART_NO,       // How many restarts
  PER_CHAFF_NO,     // How many calls to chaff-like heuristics
  PER_UNIT_NO,      // How many calls to unit-based heuristics
  STATIC_PURE_NO,   // Static pure literals
  MAX_STATS
} CntStatType;       




/*****************************************************************************
 * Trace macros
 ****************************************************************************/
#define LetPropHaveValue(prop, value)\
printf("Now let [%d] have value %s at level %d\n", prop, (value > 0 ? "TT" : "FF"), _levelID)

#define PropHasValue(prop, value)\
printf("  [%d] has value %s at level %d\n", prop, (value > 0 ? "TT" : "FF"), _levelID)

#define PropIsFailed(prop, value, level)\
printf("  [%d] is %s by failed literal at level %d\n", prop, (value > 0 ? "TT" : "FF"), level)

#define RetractingProp(prop)\
printf("  Retracting [%d] at level %d\n", prop, _levelID)

#define ContradictionFoundOn(prop)\
printf("  Contradiction found on [%d] at level %d\n", prop, _levelID)

#define NewWRfrom(cl1, cl2)\
printf("  Working reason from ");\
cl1 -> PrintClause(_id2Ref);\
printf(" and ");\
cl2 -> PrintClause(_id2Ref);\
printf(" \n")

#define Becomes(wr)\
printf("  becomes ");\
wr -> PrintClause(SATinstance -> _id2Ref);\
printf(" \n")

#define Skipping(prop)\
printf("Jumping over [%d]\n", prop);

//#endif
  
#if !defined(LITERAL_H)
#define LITERAL_H

#include <iostream>



/*****************************************************************************/
/*!
   \class Literal Literal.h
   \brief This class is used to represent a literal.

   Bit 0   : watched (1) non watched (00, i.e., also bit 1 is 0).
   Bit 1   : direction of clause exploration, either 0 (decreasing towards
             the beginning) or 1 (increasing towards the end).
   Bit 2   : positive (0) negative (1).
   Rest    : value. 

   The special configuration 0x02 is reserved for the clause marker.
*/
/*****************************************************************************/
class Literal {
  int value_;
  // Raw constructor, for internal use only
  Literal(int v) {
    value_ = v;
  }
public:
  Literal() {
    // All literals are initialized as clause markers (1 is a fake value)
    value_ = (1 << 3) | 0x02;
  }
  Literal(int value, bool sign) {
    value_ = (sign ? (value << 3) : ((value << 3) | 0x04));
  }
  ~Literal() { }
  // Standard literal operations
  int getValue() const {
    return (value_ >> 3);
  }
  void setValue(int value) {
    value_ = (value << 3);
  }
  int getRealValue() const {
    return (value_);
  }
  void setRealValue(int value) {
    value_ = value ;
  }

  bool getSign() const {
    return ((value_ & 0x04) == 0);
  }
  void setSign(bool sign) {
    value_ = (sign ? value_ & ~0x04 : value_ | 0x04);
  }
  void flipSign() {
    value_ = value_ ^ 0x04;
  }
  Literal operator-() const {
    return Literal(value_ ^ 0x04);
  }
  bool isEqual(const Literal& l) {
    return (getValue() == l.getValue() && getSign() == l.getSign());
  }
  // Watching 
  void watch(int direction) {
    value_ = (direction < 0 ? (value_ | 0x01) : (value_ | 0x03));
  } 
  void unwatch() {
    value_ = value_ & ~0x03;
  } 
  bool isWatched() const {
    return ((value_ & 0x01) != 0);
  }
  void flipDirection() {
    value_ = (value_ ^ 0x02);
  }
  int readDirection() const {
    return ((value_ & 0x03) - 2);
  }  
  // Clause Marking
  int readClauseMarker() const {
    return (((value_ & 0x03) == 0x02) ? value_ >> 3 : 0);
  }
  void makeClauseMarker(int clauseIndex) {
    value_ = (clauseIndex << 3) | 0x02;
  }
  bool isClauseMarker() const {
    return ((value_ & 0x03) == 0x02);
  }
  // Compute an unsigned integer corresponding to a signed literal
  unsigned int computeIndex() {
    return (getSign() ? (2 * getValue()) : ((2 * getValue()) - 1));
  }
};
ostream& operator<< (ostream& outStream, const Literal& l);

#endif

#if !defined(VARIABLE_H)
#define VARIABLE_H

/******************************************************************************
 * Standard and user-defined includes					   
 *****************************************************************************/
//#include "simo.h"
//#include "Literal.h"

/*****************************************************************************/
/*!
   \class Variable Variable.h
   \brief This class is used to represent a variable.
*/
/*****************************************************************************/
class Variable {
  friend class Solver;
  friend class Clauses;
  
public:
  /*! Choice of values that a variable can be assigned to. */
  enum Value {
    FF = -1,    /*!< True */
    DC = 0,     /*!< Don't care */
    TT = 1      /*!< False */
  };
  Variable();
  Variable(int id);
  ~Variable() { };

  unsigned int getId( void ) const {
    return _id;
  }
  Value getValue( void ) const {
    return _value;
  }
  int getMode( void ) const {
    return _mode;
  }
  const vector<LiteralRef>& getPosWatched( void ) const {
    return _posWatched;
  }
  const vector<LiteralRef>& getNegWatched( void ) const {
    return _negWatched;
  }
  // Reason has also a set method because we must can exchange 
  // information between forward and backward phases in search.
  ClauseRef getReason( void ) const {
    return _reason;
  }
  void setReason( ClauseRef reason ) {
    _reason = reason;
  }

  bool isMatching(bool value) const {
    return ((_value == DC) ||
	    ((_value == FF) && !value) || 
	    ((_value == TT) && value));
  }
  bool isSatisfying(bool value) const {
    return (((_value == FF) && !value) || 
	    ((_value == TT) && value));
  }
  
private:
  unsigned int       _id;
  unsigned int       _mode;
  Value              _value;
  unsigned int       _level;
  vector<LiteralRef> _posWatched;
  vector<LiteralRef> _negWatched;

#ifndef CHRONO_BACKTRACK
  ClauseRef          _reason;
#endif

};

/*****************************************************************************/
/*!
   \class VariableAtLevel Variable.h
   \brief This class is used to represent a variable at a given level.
*/
/*****************************************************************************/
#ifndef CHRONO_BACKTRACK
class VarAtLevel {
  friend class Solver;
  
  VariableRef _var;
  bool        _sign;
  ClauseRef   _reason;
};
#endif

#endif

#if !defined(PARAMETERS_H)
#define PARAMETERS_H

//#include "simo.h"

class Parameters {
public:
  // Heuristic
  HeurType     heuristic;
  PeriodType   periodicHeur;
  unsigned int baseUpdateCycle;
  unsigned int updateCycle;
  unsigned int auxiliaryHeur;
  float        switchThreshold;
  // Learning
  bool         relevance;       
  unsigned int learnOrder;      
  unsigned int permanentSize;
  unsigned int deletionCycle;
  // begin MARCO
  unsigned int forgetClausesCalls;
  unsigned int minLiteralsNum;
  unsigned int maxLiteralsNum;
  // end MARCO
  // Randomness
  unsigned int seed;
  int          baseRandomness;
  int          randomness;
  // Restart
  bool         allowRestart;	
  float        nextRestartTime;	
  float        restartTimeIncr;
  float        restartTimeIncrIncr;
  unsigned int nextRestartBacktrack;
  unsigned int restartBacktrackIncr;		
  unsigned int restartBacktrackIncrIncr;
  unsigned int restartRandomness;	
  // Timeout (in CPU seconds)
  unsigned int timeout;

  Parameters() {
    heuristic       = D_PERIODIC;  // Random heuristic
    periodicHeur    = P_CHAFF;   // Use Chaff scores with periodic heuristic
    baseUpdateCycle = 255;      // Default update cycle
    auxiliaryHeur   = 0;        // Extra parameter for heuristics
    switchThreshold = 0.9;      // Used by GMT0i to switch from Chaff to Unit
    relevance       = true;    
    learnOrder      = 20;       // Tolerate up to 20 open or subsumed literals
    permanentSize   = 4;        // Do not delete clauses with less than 4 lits
    deletionCycle   = 5000;     // Sweep clauses every 5000 backtracks
    // begin MARCO
    forgetClausesCalls       = 0;
    minLiteralsNum       = 100;
    maxLiteralsNum        = 5000;
    // end MARCO
    seed            = 1;        // No particular seed    
    baseRandomness  = 0;         
    allowRestart             = false;  // Allow restart
    nextRestartTime          = 50;    // Wait 50 seconds between restarts
    restartTimeIncr          = 0;
    restartTimeIncrIncr      = 0;
    nextRestartBacktrack     = 0;
    restartBacktrackIncr     = 40000;		
    restartBacktrackIncrIncr = 100;
    restartRandomness        = 0;
    timeout                  = 12000;
    return;
  }
  ~Parameters() { }
  void ParseCmdLine(int argc, char * argv[]);
  void GiveHelp(char * argv[]);
  void OutputDimacs();
};

#endif


#if !defined(CHOOSE_VARIABLE_H)
#define CHOOSE_VARIABLE_H

//#include "simo.h"
//#include "Solver.h"

class VariableData {
  friend class ChooseVariable;
  friend class Solver;
public :
  VariableData( void );
  VariableData( VariableRef var );
  ~VariableData( void ) { };

private :
  VariableRef        _var;
  unsigned int       _posLitsCount;
  unsigned int       _negLitsCount;
  unsigned int       _oldPosLitsCount;
  unsigned int       _oldNegLitsCount;
  int                _posScore;
  int                _negScore;
  unsigned int       _priority;
};

typedef pair<VariableData*,unsigned int> Priority;  

class ChooseVariable {
  friend class Solver;
public :
  ChooseVariable( Solver* solver, Parameters& params );
  ~ChooseVariable( void ) { };

  VariableRef operator()( Variable::Value& value, int& mode );

  // Observing the search process
  void onAddVariable(VariableRef var);
  void onAddLiteral(const Literal& l);
  void onRetractProp(const VariableRef var);
  void onBacktrack( void );
  void beforeRestart( void );
  void afterRestart( void );

  // Run time adjustments
  void doRuntimeInitialization( void );

  // Print methods
  void PrintPriorityQueue( void );

private :
  // Heuristics
  VariableRef StaticHeuristic(Variable::Value& value, int &mode);
  VariableRef RandomHeuristic(Variable::Value& value, int &mode);
  VariableRef UnitHeuristic(Variable::Value& value, int &mode);
  VariableRef PeriodicHeuristic(Variable::Value& value, int &mode);

  // Dilemma propagation
  bool DilemmaPropagate(VariableRef hypVar);

  // Update heuristics data
  inline void periodicChaffUpdateStats() {
    if ( params_.periodicHeur == P_CHAFF ) {
      periodicChaffOnlyUpdateStats();
    } else {
      periodicChaffGMTUpdateStats();
    }
  }
  void periodicChaffGMTUpdateStats();
  void periodicGMT01UpdateStats();
  void periodicGMT02UpdateStats();
  void periodicGMT03UpdateStats();
  void periodicChaffOnlyUpdateStats( void );
  void periodicUnitUpdateStats( void );
  
  // Special purpose look-ahead and look-back
  bool leanUnitPropagate(vector<Implied>& auxStack, 
			 unsigned int& binCount, unsigned int& unitCount);
#ifndef CHRONO_BACKTRACK
  void leanBacktrack(vector<Implied>& auxStack, bool isFailed) {
    return (isFailed ? 
	    leanBtWithReason(auxStack) : leanBtWithoutReason(auxStack));
  }
#else
  void leanBacktrack(vector<Implied>& auxStack, bool isFailed) {
    return leanBtWithoutReason(auxStack);
  }
#endif
  
  void leanBtWithReason(vector<Implied>& auxStack);
  void leanBtWithoutReason(vector<Implied>& auxStack);
  ClauseRef CreateDilemmaWr(vector<Implied>& _auxStack, Literal dilemma);

  // The solver
  Solver*      solver_;
  Parameters&  params_;

  vector<VariableData*> variablesData_;
  vector<VariableData*> id2DataRef_;

  vector<Implied>  _auxStackTT;       // Auxiliary stacks for failed
  vector<Implied>  _auxStackFF;       // literal detection and dilemma

  typedef vector<bool> bit_vector;
  bit_vector       _dilemmaCheck;     // Dilemma flags
  vector<Implied>  _dilemmaStack;     // Dilemma stack
  
  bool             _mustBacktrack;    // Backtracking must occur

  unsigned int 	   _maxPriorityIdx;
  vector<Priority> _varPriorityQueue;  

};

#endif


#if !defined(CLAUSE_H)
#define CLAUSE_H

/******************************************************************************
 * Standard and user-defined includes					   
 *****************************************************************************/
//#include "simo.h"
//#include "Literal.h"
//#include "Variable.h"

/*****************************************************************************/
/*!
   \class Clause Clause.h
   \brief This class is used to represent a Clause.
*/
/*****************************************************************************/
class Clauses {
  friend class Solver;
  
  int          _id;
  unsigned int _size;
  LiteralRef   _base;

public:
  Clauses();
  Clauses(int id, int capacity);
  Clauses(ClauseRef res1, ClauseRef res2, int varId);
  Clauses(ClauseRef res1, ClauseRef res2, int varId, 
	 vector<VariableRef>& i2r, bool& hasUip);
  Clauses(int numAtoms, int * reason, int sizeReason);
  //Clauses(vector<VariableRef>& i2r, bool * assignments, int sizeReason);
  //Clauses(vector<VariableRef>& searchSt);
  ~Clauses() { 
    delete[](_base -1); 
  }
  int getId( void ) const {
    return _id;
  }
  int getSize( void ) const {
    return _size;
  }
  void PushLiteral(const Literal &l);
  void Close();
  bool HasMember(int varId);
  bool isUnit(vector<VariableRef>& i2r);
  bool isBinary(vector<VariableRef>& i2r);
  void PrintClause(vector<VariableRef>& i2r);
  void PrintClauseSimplified(vector<VariableRef>& i2r);
  void PrintClauseDimacs(FILE * outFile);
};

#endif




#if !defined(STATISTICS_H)
#define STATISTICS_H

//#include "simo.h"

class Statistics {
public:
  unsigned int   counting[MAX_STATS];
  float          timing[MAX_TIMERS];

  Statistics();
  ~Statistics() { }
};

#endif


//#if !defined(STRATEGY_H)
//#define STRATEGY_H

//class Strategy {

//public :  
  /*! The result of applying the strategy and the ancillary methods. */
//enum Result {
//FALSE = -2,        /*!< Definitely inconsistent */
//INCONSISTENT = -1, /*!< Inconsistent */ 
//CONSISTENT = 0,    /*!< Consistent */
//TRUE = 1           /*!< Definitely consistent */
//}
  
//virtual Result operator()( void ) = 0;

//} // End of class Strategy

//#endif
    

#if !defined(TIMERSIMO_H)
#define TIMERSIMO_H

/******************************************************************************
 * Standard and user-defined includes					   
 *****************************************************************************/
#ifdef _WIN32	// marcy
#include <ctime>
#else
#include <sys/time.h>
#include <sys/resource.h>
#endif
#include <unistd.h>
#include <signal.h>


/*****************************************************************************/
/*!
   \class TimerSimo TimerSimo.h
   \brief This class is used to measure elapsed CPU time
*/
/*****************************************************************************/
class TimerSimo {
  
#ifdef _WIN32	// marcy
  float ru1, ru2, ru;
  int r;
#else
  struct rusage ru1, ru2, ru;
  struct rlimit r;
#endif
  
public:
  float Epoch();
  void  Start();
  float Elapsed();
  void  SetTimeout(int seconds, void(*handler)(int));
};


#endif

#if !defined(SOLVER_H)
#define SOLVER_H

//#include "simo.h"
//#include "Literal.h"
//#include "Variable.h"
//#include "Clause.h"
//#include "Parameters.h"
//#include "Statistics.h"
//#include "TimerSimo.h"

class Solver {
  
  friend class ChooseVariable;
  friend class Clauses;
/******************************************************************************
 * Class Solver public interface
 *****************************************************************************/
public:


  /*! How many ways to assign a variable. */
  enum Mode {
    CH = 0,       /*!< Non-deterministic choice */
    DE = 1        /*!< Deduction */
  };



  //  /*! Returned values. */
  // UNSAT   = -1, /*!< Unsatisfiable */
  //UNKNOWN = 0,  /*!< Undetermined */
  //SAT     = 1   /*!< Satisfiable */

  //  enum Result {
  // UNSAT   = -1, 
  //UNKNOWN = 0,  
  //SAT     = 1   
  //};

  // Constructors and destructor
  Solver(int varNum, int clNum);
  Solver(FILE * inFile, bool erase); 
  ~Solver();

  // Clause uploading
  void        AddCheckedClause(vector<int>& lits);

  // Operations

  //void        Reset(); 

  Result      Solve( void );
  bool        ExtendProp( const VariableRef var, 
			  const Variable::Value value, const int mode );
  void        RetractProp( const VariableRef var );
  bool        leanExtendProp( vector<Implied>& auxStack, 
			      VariableRef var, Variable::Value value, int mode,
			      unsigned int& binCount );
  void        leanRetractProp( VariableRef var );
  bool        UnitPropagate( void );
  VariableRef Backtrack(Variable::Value& value, int& mode,bool);
  void        Restart(void);
  bool        FormulaIsEmpty() { return (_openVarNum == 0); };

  // Messa qui per evitare problemi
  void _dynamicInitSolver();

  // Miscellaneous modifiers/accessors
  void GetModel(vector<int>& modelAsInts);
  void GetChoices(vector<int>& modelAsInts);
  int GetLevel( void ) {
    return _levelID;
  }
  void SetOptions( int argc, char* argv[] ) { 
    _params.ParseCmdLine(argc, argv);
  }
  void DisplayOptions( char * argv[] ) {
    _params.GiveHelp(argv);
  }
  size_t GetModelSize( void ) { 
    return _searchStack.size(); 
  }
  size_t GetVariableNum( void ) { 
    return _variables.size(); 
  }
  void SetTimeoutHandler( void(*handler)(int) ) { 
    _handler = handler; 
  }
  int GetCntStatistic( CntStatType stat ) { 
    return (_stats.counting[stat]); 
  }
  float GetTimeStatistic( TimeStatType stat ) { 
    return (_stats.timing[stat]); 
  }
  pair< ClauseRef, ClauseRef > getConflictClauses( void ) {
    return make_pair(_conflictCl1, _conflictCl2);
  }
  VariableRef getConflictVariable( void ) {
    return _conflictVar;
  }

  // Miscellaneous output methods
  void PrintStatsDimacs(Result result);
  void PrintStats(Result result);
  void PrintStatsCmodels(bool * assignments, int * modes); 
  //  void PrintStatsCmodels();
  void PrintStack();
  void PrintClauses();
  void PrintSomeClauses(size_t begin, size_t end); 
  void PrintSimplified();
  void PrintPriorityQueue();
  void PrintUnitAtLevel();

  Statistics   _stats;
  TimerSimo        _timer;

  // Variable selection
  ChooseVariable*          chooseVariable_;
  vector<ClauseRef>         _latestLearned;    // Latest learned clauses (temp)
  int  _levelID;                               // The current decision level

  // Search
  vector<VariableRef>       _searchStack;      // Search stack
  vector<Implied>           _unitStack;        // Look-ahead stack  


  bool _heurfalse;

  bool _stop;
  bool _forceBT;
  bool _bjOccur;                               // To be used in GMT0i
  vector<VariableRef>       _id2Ref;           // Index to reference
#ifndef CHRONO_BACKTRACK
  void ScanLearned(ClauseRef learnedCl);
  bool UnitPropagateLearned();
#endif
/******************************************************************************
 * Class Solver private interface
 *****************************************************************************/
private:

  // Formula representation
  vector<VariableRef>       _variables;        // The set of all variables
  vector<ClauseRef>         _clauses;          // The set of all clauses

  // Backjumping and learning
#ifndef CHRONO_BACKTRACK
  ClauseRef                 _conflictCl1;      // First conflicting reason 
  ClauseRef                 _conflictCl2;      // Second conflicting reason 
  VariableRef               _conflictVar;      // Conflicting variable

  multimap<int, VarAtLevel> _unitAtLevel;      // Out-of-level learned units
  vector<ClauseRef>         _toDelete;
#endif
  // Bookkeeping
  int  _varNum;
  int  _openVarNum;
  int  _clNum;


  //bool _enum;
  // Statistics, Parameters & timeout handling
  Parameters   _params;


  void         (*_handler)(int);

  // Real constructors
  void _staticInitSolver();
  //void _dynamicInitSolver();
  
  // Periodic tasks (e.g. forgetting clauses, restarts, etc.)
  void periodicCheckRestart();
#ifndef CHRONO_BACKTRACK
  void periodicForgetClauses();
#endif

  // Learning
#ifndef CHRONO_BACKTRACK
  void LearnClause(ClauseRef learnedCl);
#endif

};

#endif

//#if !defined(INTEGRAT_H) 
//#define INTEGRAT_H 

void Reset(void);

void loadFormula(char *, bool, bool, bool *, int);
void Print();
Result SingleSolve();
//void PrintRes();
//void BacktrackWithReason();
void PrintRes(bool *, int *);
// In simo1.cpp was:
//void BacktrackWithReason(bool *, int);
//void BacktrackWithReason(bool, int *, int);
void BacktrackWithReason(bool, int *, int *, int, int, bool);
//#include "integration.h" 


#endif 



