#ifndef SMTSOLVER_H_
#define SMTSOLVER_H_

#include "boost/process/detail/child_decl.hpp"
#include "boost/process/pipe.hpp"
#include "defines.h"
#include "glog/logging.h"
#include "param.h"
#include "program.h"
#include "logics/logic.h"
#include "logics/QF_LIA_logic.h"
#include <boost/process.hpp>
#include <chrono>
#include <memory>
#include <regex>


class SolverResult {
  public:
    bool isSatisfiable;
    map<Atom*, bool> atomAssignments;
    map<SymbolicTerm*, string> constraintVariableAssignments;
    map<MinimizationStatement*, string> minimizationAtomAssignments;

    chrono::milliseconds solveDuration;
    chrono::milliseconds getValuesDuration;
};

class Solver {
public:
  void callSMTSolver(Param &params, Program &program);

private:
  bool parseSolverResults(boost::process::ipstream &inputStream,
                                   vector<string> &resultAnswerSet,
                                   map<string, string> &resultMinimizationValues);
  string getProgramBodyString(Program &program);
  string getAnswerNegationString(SolverResult& result, bool includeConstraintVariables);
  string getMinimizationAssertionString(map<MinimizationStatement*,string> &minimizationResults);
  void writeToFile(string input, string outputFileName);

  ILogic* logic;
};

class SMTProcess {
public:
  SMTProcess(SMTSolverCommand solverCommand);
  SMTProcess(string solverCommand);

  void Send(string body);
  unique_ptr<SolverResult> CheckSatAndGetAssignments(list<Atom*> &atoms, list<SymbolicTerm*> &constraintVariables, list<MinimizationStatement*> &minimizations);
private:
  SMTSolverCommand solverOption;
  boost::process::ipstream output;
  boost::process::opstream input;
  boost::process::child process;

  map<string, string> getRawAssignments(list<string> &variableNames);
};

#endif // SMTSOLVER_H_
