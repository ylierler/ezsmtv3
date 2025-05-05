#ifndef SMTPROCESS_H_
#define SMTPROCESS_H_

#include "boost/process/detail/child_decl.hpp"
#include "boost/process/pipe.hpp"
#include <boost/process.hpp>
#include "defines.h"
#include "solver/smtsolver.h"

using namespace std;

class SMTProcess {
public:
  SMTProcess(SMTSolverCommand solverCommand);
  SMTProcess(string solverCommand);

  void Send(string body);
  unique_ptr<SolverResult> CheckSatAndGetAssignments(Program program, list<SymbolicTerm*> &constraintVariables, Param params);
private:
  SMTSolverCommand solverOption = NO_VALUE;
  vector<string> solvers = {"CVC4", "CVC5", "Z3", "YICES"};
  boost::process::ipstream output;
  boost::process::opstream input;
  boost::process::child process;

  map<string, string> getRawAssignments(list<string> &variableNames);
  void startChildProcess(string solverCommand);
  void setSolverOption(string solverCommand);
};

#endif // SMTPROCESS_H_
