#include "smtsolver.h"
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

namespace bp = boost::process;

void logIterationResults(int roundNumber, SolverResult& results, chrono::milliseconds totalRoundDuration) {
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

// call EZSMT and SMT solver
void Solver::callSMTSolver(Param &params, Program &program) {
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

  auto roundStart = chrono::high_resolution_clock::now();

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
    auto roundEnd = chrono::high_resolution_clock::now();
    logIterationResults(i, *result, chrono::duration_cast<chrono::milliseconds>(roundEnd - roundStart));
    roundStart = chrono::high_resolution_clock::now();

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
  // TODO Support priorities
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
    output << "(assert " << c->toSmtLibString() << ")" << endl;
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

SMTProcess::SMTProcess(SMTSolverCommand type) {
  solverOption = type;

  string solverCommand;
  if (type == CVC4)
    solverCommand =
        "../tools/cvc4 --lang smt --output-lang smt --incremental";
  else if (type == CVC5)
    solverCommand =
        "../tools/cvc5 --lang smt --output-lang smt --incremental";
  else if (type == Z3)
    solverCommand = "../tools/z3-4.8.17 -smt2 -in";
  else if (type == YICES)
    solverCommand = "../tools/yices-smt2 ";

  VLOG(3) << "Starting child process for solver: " << solverCommand;
  process = bp::child(solverCommand, bp::std_out > output, bp::std_in < input);
}

SMTProcess::SMTProcess(string customSolverCommand) {
  VLOG(3) << "Starting child process for solver: " << customSolverCommand;
  process = bp::child(customSolverCommand, bp::std_out > output, bp::std_in < input);
}

void SMTProcess::Send(string body) {
  VLOG(3) << "Sending to SMT process: " << body;
  input << body << endl;
}

unique_ptr<SolverResult> SMTProcess::CheckSatAndGetAssignments(list<Atom*> &atoms, list<SymbolicTerm*> &constraintVariables, list<MinimizationStatement*> &minimizations) {
  auto result = unique_ptr<SolverResult>(new SolverResult());

  auto solveStart = chrono::high_resolution_clock::now();
  Send("(check-sat)");
  auto solveEnd = chrono::high_resolution_clock::now();
  result->solveDuration = chrono::duration_cast<chrono::milliseconds>(solveEnd - solveStart);

  string satResult;
  std::getline(output, satResult);
  VLOG(3) << "Read check sat result: " << satResult;
  if (satResult != "unsat" && satResult != "sat") {
    LOG(FATAL) << "Got unexpected result from SMT solver: " << satResult;
  }

  if (satResult == "unsat") {
    result->isSatisfiable = false;
    return result;
  }

  result->isSatisfiable = true;

  auto getValuesStart = chrono::high_resolution_clock::now();

  // Atoms
  list<string> atomNames;
  transform(atoms.begin(), atoms.end(), std::back_inserter(atomNames), [](Atom* a) { return a->getSmtName(); });
  auto rawAtomAssignments = getRawAssignments(atomNames);
  for (Atom* atom : atoms) {
    string atomName = atom->getSmtName();
    if (rawAtomAssignments.find(atomName) != rawAtomAssignments.end()) {
      result->atomAssignments[atom] = rawAtomAssignments[atomName] == "true" ? true : false;
    }
  }

  // Constraint variables
  list<string> variableNames;
  transform(constraintVariables.begin(), constraintVariables.end(), std::back_inserter(variableNames), [](SymbolicTerm* t) { return t->name; });
  auto rawVariableAssignments = getRawAssignments(variableNames);
  for (SymbolicTerm* variable : constraintVariables) {
    if (rawVariableAssignments.find(variable->name) != rawVariableAssignments.end()) {
      result->constraintVariableAssignments[variable] = rawVariableAssignments[variable->name];
    }
  }

  // Minimization statements
  list<string> minimizationAtomNames;
  transform(minimizations.begin(), minimizations.end(), std::back_inserter(minimizationAtomNames), [](MinimizationStatement* m) { return m->getSmtAtomName(); });
  auto rawMinimizationAssignments = getRawAssignments(minimizationAtomNames);
  for (auto minimization : minimizations) {
    string atomName = minimization->getSmtAtomName();
    if (rawMinimizationAssignments.find(atomName) != rawMinimizationAssignments.end()) {
      result->minimizationAtomAssignments[minimization] = rawMinimizationAssignments[atomName];
    }
  }

  auto getValuesEnd = chrono::high_resolution_clock::now();
  result->getValuesDuration = chrono::duration_cast<chrono::milliseconds>(getValuesEnd - getValuesStart);

  return result;
}

map<string, string> SMTProcess::getRawAssignments(list<string> &variableNames) {
  if (variableNames.empty()) {
    return map<string, string>();
  }

  stringstream getValueStatement;
  getValueStatement << "(get-value (";
  for (string variableName : variableNames) {
    getValueStatement << variableName << " ";
  }
  getValueStatement << "))";

  Send(getValueStatement.str());

  // Concat multi-line output to single line
  stringstream singleLineStream;
  string line;
  while (std::getline(output, line)) {
    VLOG(3) << "Read line from solver: " << line;
    singleLineStream << line;

    // This is a hacky workaround to handle z3's multiline output
    if (line[line.length() - 2] == ')' && line[line.length() - 1] == ')') {
      break;
    }
  }
  string assignmentsLine = singleLineStream.str();
  map<string,string> rawAssignments;

  SymbolicExpressionParser parser;
  auto assignmentsList = parser.ParseSymbolList(assignmentsLine);
  for (auto a : assignmentsList->children) {
    auto assignment = dynamic_cast<SymbolList*>(a);
    auto variable = dynamic_cast<Symbol*>(assignment->children.front());
    auto value = dynamic_cast<ISymbolicExpression*>(assignment->children.back());

    VLOG(3) << "Parsed assignment: " << variable->ToString() << "=" << value->ToString();
    rawAssignments[variable->content] = value->ToString();
  }

  return rawAssignments;
}
