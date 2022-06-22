#ifndef SMTSOLVER_H_
#define SMTSOLVER_H_

#include "boost/process/detail/child_decl.hpp"
#include "boost/process/pipe.hpp"
#include "defines.h"
#include "param.h"
#include "program.h"
#include "smtlogics.h"
#include <boost/process.hpp>

class SolverResult {
  public:
    SolverResult(bool isSatisfiable) {
      this->isSatisfiable = isSatisfiable;
    }

    bool isSatisfiable;
    map<Atom*, bool> atomAssignments;
    map<SymbolicTerm*, string> constraintVariableAssignments;
};

class Solver {
public:
  void callSMTSolver(Param &params, Program &program);

private:
  bool parseSolverResults(boost::process::ipstream &inputStream,
                                   vector<string> &resultAnswerSet,
                                   map<string, string> &resultMinimizationValues);
  string getProgramBodyString(Program &program);
  string getCheckSatString(Program &program);
  string getAnswerNegationString(SolverResult& result, bool includeConstraintVariables);
  string getMinimizationAssertionString(map<string,string> &minimizationResults);
  void writeToFile(string input, string outputFileName);

  // FIXME
  QF_LIA logic;
};


class SMTProcess {
public:
  SMTProcess(SMTSolverCommand solverCommand);
  void Send(string body);
  SolverResult CheckSatAndGetAssignments(list<Atom*> atoms, list<SymbolicTerm*> constraintVariables);
private:
  SMTSolverCommand solverOption;
  boost::process::ipstream output;
  boost::process::opstream input;
  boost::process::child process;

  map<string, string> getRawAssignments(list<string> variableNames);

};

#endif // SMTSOLVER_H_
