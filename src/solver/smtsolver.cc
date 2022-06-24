#include "smtsolver.h"
#include "symbolicexpressionparser.h"
#include "defines.h"
#include "theory.h"
#include "timer.h"
#include <algorithm>
#include <boost/process.hpp>
#include <chrono>
#include <cstring>
#include <fstream>
#include <glog/logging.h>
#include <iostream>
#include <iterator>
#include <map>
#include <ostream>
#include <ratio>
#include <regex>
#include <sstream>
#include <unistd.h>
#include "solver/smtprocess.h"

using namespace chrono;

void logIterationResults(int roundNumber, SolverResult& results, milliseconds totalRoundDuration) {
  if (VLOG_IS_ON(1)) {
    cout << "Answer " << roundNumber << ": ";
  }

  int displayedAtoms = 0;
  for (auto assignment : results.atomAssignments) {
    auto atom = assignment.first;
    bool atomSign = assignment.second;
    if (atomSign && (atom->showInOutputAnswerSet || VLOG_IS_ON(3))) {
      cout << atom->atom_name() << " ";
      displayedAtoms++;
    }
  }

  if (displayedAtoms == 0) {
    cout << "{}";
  }

  cout << endl;

  if (!results.constraintVariableAssignments.empty()) {
    for (auto assignment : results.constraintVariableAssignments) {
      cout << assignment.first->name << "=" << assignment.second << " ";
    }
    cout << endl;
  }

  if (VLOG_IS_ON(1) && !results.minimizationAtomAssignments.empty()) {
    cout << "Minimization: ";
  }

  if (!results.minimizationAtomAssignments.empty()) {
    for (auto minimization : results.minimizationAtomAssignments) {
      cout << minimization.second;
    }
    cout << endl;
  }

  VLOG(1) << "Finished round " << roundNumber << " in " << totalRoundDuration.count() << "ms";
  VLOG(1) << "  " << results.solveDuration.count() << "ms SMT Check Satisfiability";
  VLOG(1) << "  " << results.getValuesDuration.count() << "ms SMT Get Values";

  // Add newline between iterations
  cout << endl;
}

void Solver::SolveProgram(Param &params, Program &program) {
  list<TheoryStatement*> theoryStatements;
  for (auto pair : program.theoryStatements) {
    theoryStatements.push_back(pair.second);
  }

  this->logic = new QF_LIA_logic();
  this->logic->processTheoryStatements(theoryStatements);

  string programBody = getProgramBodyString(program);

  // Override -s option with --solver-command if provided
  auto solverProcess = !params.smtSolverCommand.empty() ? SMTProcess(params.smtSolverCommand) : SMTProcess(params.SMTsolver);

  solverProcess.Send(programBody);
  if (VLOG_IS_ON(3)) {
    cout << "Wrote program body:" << endl << programBody;
  }

  auto constraintVariables = logic->getConstraintVariables();
  list<Atom*> atoms(program.atoms.begin(), program.atoms.end());

  auto roundStart = high_resolution_clock::now();

  int i = 1;
  for (;; i++) {
    auto result = solverProcess.CheckSatAndGetAssignments(atoms, constraintVariables, program.minimizations);

    if (i == 1) {
      LOG(INFO) << (result->isSatisfiable ? "SAT" : "UNSAT");
    }

    if (!result->isSatisfiable) {
      break;
    }

    // Only log timer results if SAT
    auto roundEnd = high_resolution_clock::now();
    logIterationResults(i, *result, duration_cast<milliseconds>(roundEnd - roundStart));
    roundStart = high_resolution_clock::now();

    if (params.answerSetsToEnumerate != 0 &&
        params.answerSetsToEnumerate == i) {
      break;
    }

    if (!result->minimizationAtomAssignments.empty()) {
      auto minimizationAssertion = getMinimizationAssertionString(result->minimizationAtomAssignments);
      solverProcess.Send(minimizationAssertion);
    }

    auto answerSetNegation = getAnswerNegationString(*result, params.includeConstraintsInEnumeration);
    solverProcess.Send(answerSetNegation);
  }
}

string Solver::getAnswerNegationString(SolverResult& result, bool includeConstraintVariables) {
  if (result.atomAssignments.size() == 0) {
    LOG(FATAL) << "Cannot create answer negation for empty set";
  }

  ostringstream output;
  output << "(assert (not (and";

  for (pair<Atom*, bool> atomAssignment : result.atomAssignments) {
    string atomName = atomAssignment.first->getSmtName();
    output << " ";
    if (atomAssignment.second) {
      output << atomName;
    } else {
      output << "(not " << atomName << ")";
    }
  }

  if (includeConstraintVariables && result.constraintVariableAssignments.size() > 0) {
    for (pair<SymbolicTerm*, string> variableAssignment : result.constraintVariableAssignments) {
      output << " (= " << variableAssignment.first->name << " " << variableAssignment.second << ")";
    }
  }

  output << ")))" << endl;

  return output.str();
}

string Solver::getMinimizationAssertionString(map<MinimizationStatement*,string> &minimizationResults) {
  ostringstream output;
  output << "(assert (or ";
  for (auto minimization : minimizationResults) {
    output << "(< " << minimization.first->getSmtAtomName() << " " << minimization.second << ") ";
  }
  output << "))" << endl;

  return output.str();
}

// FIXME this is copying strings
string Solver::getProgramBodyString(Program &program) {
  ostringstream output;

  output << "(set-info :smt-lib-version 2.6)" << endl;
  output << "(set-option :produce-assignments true)" << endl;
  output << "(set-logic " << logic->SMT_LOGIC_NAME() << ")" << endl;

  for (Atom *a : program.atoms) {
    output << "(declare-const " << a->getSmtName() << " Bool)" << endl;
  }
  logic->getDeclarationStatements(output);

  for (Clause *c : program.clauses) {
    output << "(assert " << toSMTString(c) << ")" << endl;
  }
  logic->getAssertionStatements(output);

  for (MinimizationStatement *m : program.minimizations) {
    output << "(declare-const " << m->getSmtAtomName() << " Int)" << endl;
    output << "(assert (= " << m->getSmtAtomName() << " (+";
    for (MinimizationAtom *a : m->atoms) {
      output << " (ite " << a->atom.getSmtName() << " " << a->weight << " 0)";
    }
    output << ")))" << endl;
  }

  return output.str();
}

string Solver::toSMTString(Clause *clause) {
  ostringstream expression;
  Atom **a;

  expression << "(or";

  for (a = clause->nbody; a != clause->nend; a++) {
    string atomName = (*a)->getSmtName();
    expression << " (not " << atomName << ")";
  }
  for (a = clause->pbody; a != clause->pend; a++) {
    string atomName = (*a)->getSmtName();
    expression << " " << atomName;
  }

  expression << ")";

  return expression.str();
}
