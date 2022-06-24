#include "smtsolver.h"
#include "defines.h"
#include "theory.h"
#include "timer.h"
#include <algorithm>
#include <boost/process.hpp>
#include <cstring>
#include <fstream>
#include <glog/logging.h>
#include <iostream>
#include <iterator>
#include <map>
#include <ostream>
#include <regex>
#include <sstream>
#include <unistd.h>

namespace bp = boost::process;

// TODO separate SMT-LIB writing logic from SMT solver process interaction for easier unit testing


void logIterationResults(int roundNumber, SolverResult& results, Timer &roundTimer) {
  // TODO
  // if (VLOG_IS_ON(1) && !minimizationValues.empty()) {
  //   cout << "Minimization: ";
  // }

  // if (!minimizationValues.empty()) {
  //   for (auto minimization : minimizationValues) {
  //     cout << minimization.second;
  //   }
  //   cout << " : ";
  // }

  if (VLOG_IS_ON(1)) {
    cout << "Answer " << roundNumber << ": ";
  }

  for (auto assignment : results.atomAssignments) {
    if (assignment.second) {
      cout << assignment.first->atom_name() << " ";
    }
  }
  cout << endl;

  for (auto assignment : results.constraintVariableAssignments) {
    cout << assignment.first->name << "=" << assignment.second << " ";
  }
  cout << endl;

  VLOG(2) << "Finished round " << roundNumber << " in " << roundTimer.sec << "s "
          << roundTimer.msec << "ms";
}

// call EZSMT and SMT solver
void Solver::callSMTSolver(Param &params, Program &program) {

  // Override -s option with --solver-command if provided
  // if (!params.smtSolverCommand.empty()) {
  //   solverCommand = params.smtSolverCommand;
  // }

  list<TheoryStatement*> theoryStatements;
  for (auto pair : program.theoryStatements) {
    theoryStatements.push_back(pair.second);
  }

  this->logic = QF_LIA();
  this->logic.processTheoryStatements(theoryStatements);

  string programBody = getProgramBodyString(program);
  string programCheckSatFooter = getCheckSatString(program);

  SMTProcess solverProcess(params.SMTsolver);

  solverProcess.Send(programBody);
  if (VLOG_IS_ON(3)) {
    cout << "Wrote program body:" << endl << programBody;
  }


  auto constraintVariables = logic.getConstraintVariables();
  list<Atom*> atoms(program.atoms.begin(), program.atoms.end());

  int i = 1;
  for (;; i++) {
    Timer timer;
    timer.start();

    // map<string, string> resultMinimizationValues; TODO

    auto result = solverProcess.CheckSatAndGetAssignments(atoms, constraintVariables);

    if (i == 1) {
      LOG(INFO) << (result.isSatisfiable ? "SAT" : "UNSAT");
    }

    if (!result.isSatisfiable) {
      break;
    }

    // Only log timer results if SAT
    timer.stop();
    logIterationResults(i, result, timer);

    // TODO
    // if (!resultMinimizationValues.empty()) {
    //   auto minimizationAssertion = getMinimizationAssertionString(resultMinimizationValues);
    //   solverProcess.Send(minimizationAssertion);
    // }

    if (params.answerSetsToEnumerate != 0 &&
        params.answerSetsToEnumerate == i) {
      break;
    }

    auto answerSetNegation = getAnswerNegationString(result, params.includeConstraintsInEnumeration);
    solverProcess.Send(answerSetNegation);
  }
}


void Solver::writeToFile(string input, string outputFileName) {
  ofstream outputStream;
  outputStream.open(outputFileName);
  outputStream << input;
  outputStream.close();

  VLOG(3) << "Wrote SMT-LIB file:" << endl << input << endl;
}

bool Solver::parseSolverResults(bp::ipstream &inputStream,
                                   vector<string> &resultAnswerSet,
                                   map<string, string> &resultMinimizationValues) {
  resultAnswerSet.clear();
  resultMinimizationValues.clear();

  string satResult;
  std::getline(inputStream, satResult);
  VLOG(2) << "Read check sat result: " << satResult;
  if (satResult != "unsat" && satResult != "sat") {
    LOG(FATAL) << "Got unexpected result from SMT solver: " << satResult;
  }

  if (satResult == "unsat") {
    return false;
  }

  stringstream atomsListStream;
  string line;
  while (std::getline(inputStream, line)) {
    VLOG(2) << "Read line from solver: " << line;
    atomsListStream << line;

    // This is a hacky workaround to handle z3's multiline output
    if (line[line.length() - 2] == ')' && line[line.length() - 1] == ')') {
      break;
    }
  }
  string atomsList = atomsListStream.str();

  VLOG(3) << "Parsing assignments:";
  regex r("\\((\\|[^ ]+\\|) ([^()]+)\\)");
  smatch match;
  string::const_iterator searchStart(atomsList.cbegin());
  while (regex_search(searchStart, atomsList.cend(), match, r)) {
    searchStart = match.suffix().first;
    string variable = match[1].str();
    string value = match[2].str();
    VLOG(3) << "Found assignment " << variable << " = " << value;

    if (value == "true") {
      resultAnswerSet.push_back(variable);
    } else if (variable.find(MINIMIZATION_SMT_PREFIX) != string::npos) {
      resultMinimizationValues[variable] = value;
    }
  }

  return true;
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

  VLOG(3) << "Generated answer negation:" << endl << output.str();
  return output.str();
}

string Solver::getMinimizationAssertionString(map<string,string> &minimizationResults) {
  ostringstream output;
  // TODO Support priorities
  output << "(assert (or ";
  for (auto minimization : minimizationResults) {
    output << "(< " << minimization.first << " " << minimization.second << ") ";
  }
  output << "))" << endl;

  VLOG(3) << "Generated minimization assertion:" << endl << output.str();
  return output.str();
}

// TODO
string Solver::getCheckSatString(Program &program) {
  ostringstream output;
  output << "(check-sat)" << endl;

  output << "(get-value (";
  for (Atom *a : program.atoms) {
    if (a->showInOutputAnswerSet) {
      output << a->getSmtName() << " ";
    }
  }
  for (auto minimization : program.minimizations) {
    output << minimization->getSmtAtomName() << " ";
  }
  for (auto constraintVariable : this->logic.getConstraintVariables()) {
    output << constraintVariable->name << " ";
  }
  output << "))" << endl;

  return output.str();
}

// FIXME this is copying strings
string Solver::getProgramBodyString(Program &program) {
  ostringstream output;

  output << "(set-info :smt-lib-version 2.6)" << endl;
  output << "(set-option :produce-models true)" << endl; // TODO don't produce models for performance?
  output << "(set-option :produce-assignments true)" << endl;
  output << "(set-logic " << logic.SMT_LOGIC_NAME() << ")" << endl;

  for (Atom *a : program.atoms) {
    // FIXME Should this declare a const or fun?
    output << "(declare-const " << a->getSmtName() << " Bool)" << endl;
  }
  logic.getDeclarationStatements(output);

  for (Clause *c : program.clauses) {
    output << "(assert " << c->toSmtLibString() << ")" << endl;
  }
  logic.getAssertionStatements(output);

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

  VLOG(2) << "Starting child process for solver: " << solverCommand;

  process = bp::child(solverCommand, bp::std_out > output, bp::std_in < input);
}

void SMTProcess::Send(string body) {
  input << body << endl;
}

SolverResult SMTProcess::CheckSatAndGetAssignments(list<Atom*> atoms, list<SymbolicTerm*> constraintVariables) {
  Send("(check-sat)");

  string satResult;
  std::getline(output, satResult);
  VLOG(2) << "Read check sat result: " << satResult;
  if (satResult != "unsat" && satResult != "sat") {
    LOG(FATAL) << "Got unexpected result from SMT solver: " << satResult;
  }

  if (satResult == "unsat") {
    return SolverResult(false);
  }

  SolverResult result(true);

  list<string> atomNames;
  transform(atoms.begin(), atoms.end(), std::back_inserter(atomNames), [](Atom* a) { return a->getSmtName(); });
  auto rawAtomAssignments = getRawAssignments(atomNames);
  for (Atom* atom : atoms) {
    string atomName = atom->getSmtName();
    if (rawAtomAssignments.find(atomName) != rawAtomAssignments.end()) {
      result.atomAssignments[atom] = rawAtomAssignments[atomName] == "true" ? true : false;
    }
  }

  list<string> variableNames;
  transform(constraintVariables.begin(), constraintVariables.end(), std::back_inserter(variableNames), [](SymbolicTerm* t) { return t->name; });
  auto rawVariableAssignments = getRawAssignments(variableNames);
  for (SymbolicTerm* variable : constraintVariables) {
    if (rawVariableAssignments.find(variable->name) != rawVariableAssignments.end()) {
      result.constraintVariableAssignments[variable] = rawVariableAssignments[variable->name];
    }
  }

  return result;
}

map<string, string> SMTProcess::getRawAssignments(list<string> variableNames) {

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
    VLOG(2) << "Read line from solver: " << line;
    singleLineStream << line;

    // This is a hacky workaround to handle z3's multiline output
    if (line[line.length() - 2] == ')' && line[line.length() - 1] == ')') {
      break;
    }
  }
  string assignmentsLine = singleLineStream.str();
  map<string,string> rawAssignments;

  SMTExpressionParser parser;
  auto assignmentsList = parser.ParseListExpression(assignmentsLine);
  for (auto a : assignmentsList->children) {
    auto assignment = dynamic_cast<SMTList*>(a);
    auto variable = dynamic_cast<SMTVariable*>(assignment->children.front());
    auto value = dynamic_cast<ISMTExpression*>(assignment->children.back());

    VLOG(2) << "Parsed assignment: " << variable->ToString() << "=" << value->ToString();
    rawAssignments[variable->content] = value->ToString();
  }

  return rawAssignments;
}
