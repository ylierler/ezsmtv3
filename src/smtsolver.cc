#include "smtsolver.h"
#include "timer.h"
#include <boost/process.hpp>
#include <cstring>
#include <fstream>
#include <glog/logging.h>
#include <iostream>
#include <map>
#include <ostream>
#include <regex>
#include <sstream>
#include <unistd.h>

namespace bp = boost::process;

// call EZSMT and SMT solver
void SMTSolver::callSMTSolver(Param &params, Program &program) {
  string solverCommand = "";
  if (params.SMTsolver == CVC4)
    solverCommand =
        "../tools/cvc4 --lang smt --output-lang smt --incremental";
  else if (params.SMTsolver == CVC5)
    solverCommand =
        "../tools/cvc5 --lang smt --output-lang smt --incremental";
  else if (params.SMTsolver == Z3)
    solverCommand = "../tools/z3-4.8.17 -smt2 -in";
  else if (params.SMTsolver == YICES)
    solverCommand = "../tools/yices-smt2 ";

  // Override -s option with --solver-command if provided
  if (!params.smtSolverCommand.empty()) {
    solverCommand = params.smtSolverCommand;
  }

  if (params.answerSetsToEnumerate == 1) {

  }

  stringstream ss;

  string smtFileName = "output.smt";

  string programBody = getProgramBodyString(program);
  string programCheckSatFooter = getCheckSatString(program);

  bp::ipstream solverOutput;
  bp::opstream solverInput;

  VLOG(2) << "Starting child process for solver: " << solverCommand;
  bp::child solverProcess(solverCommand, bp::std_out > solverOutput,
                          bp::std_in < solverInput);

  solverInput << programBody;
  if (VLOG_IS_ON(3)) {
    cout << "Wrote program body:" << endl << programBody;
  }

  int i = 1;
  for (;; i++) {
    VLOG(2) << "SMT solver, iteration " << i;
    Timer timer;
    timer.start();

    solverInput << programCheckSatFooter << endl;
    VLOG(3) << "Wrote check sat footer:" << endl << programCheckSatFooter;

    vector<string> resultAnswerSets;
    map<string, string> resultMinimizationValues;
    bool isSatisfiable = parseSolverResults(solverOutput, resultAnswerSets, resultMinimizationValues);

    if (!isSatisfiable) {
      break;
    }

    if (params.answerSetsToEnumerate != 1) {
      cout << "Answer " << i << ": ";
    }


    for (auto smtAtom : resultAnswerSets) {
      cout << smtAtom.substr(1, smtAtom.size() - 2) << " ";
    }
    cout << endl;

    auto answerSetNegation = getAnswerSetNegationString(resultAnswerSets);
    solverInput << answerSetNegation;

    if (!resultMinimizationValues.empty()) {
      auto minimizationAssertion = getMinimizationAssertionString(resultMinimizationValues);
      solverInput << minimizationAssertion;

      cout << "Minimization: ";
      for (auto minimization : resultMinimizationValues) {
        cout << minimization.second;
      }
      cout << endl;
    }

    timer.stop();
    VLOG(2) << "Finished round " << i << " in " << timer.sec << "s "
            << timer.msec << "ms";

    if (params.answerSetsToEnumerate != 0 &&
        params.answerSetsToEnumerate == i) {
      break;
    }
  }
}

void SMTSolver::writeToFile(string input, string outputFileName) {
  ofstream outputStream;
  outputStream.open(outputFileName);
  outputStream << input;
  outputStream.close();

  VLOG(3) << "Wrote SMT-LIB file:" << endl << input << endl;
}

bool SMTSolver::parseSolverResults(bp::ipstream &inputStream,
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

string SMTSolver::getAnswerSetNegationString(vector<string> &answerSet) {
  // TODO Should I include negatives (false)?

  ostringstream output;
  // output << "(push 1)" << endl; // TODO Is this needed?
  output << "(assert (not (and";
  for (string smtAtom : answerSet) {
    output << " " << smtAtom;
  }
  output << ")))" << endl;

  VLOG(3) << "Generated answer set negation:" << endl << output.str();
  return output.str();
}

string SMTSolver::getMinimizationAssertionString(map<string,string> &minimizationResults) {
  ostringstream output;
  // TODO Support priorities
  output << "(assert (or ";
  for (auto minimization : minimizationResults) {
    output << "(<= " << minimization.first << " " << minimization.second << ") ";
  }
  output << "))" << endl;

  VLOG(3) << "Generated minimization assertion:" << endl << output.str();
  return output.str();
}

string SMTSolver::getCheckSatString(Program &program) {
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
  output << "))" << endl;

  return output.str();
}

// FIXME this is copying strings
string SMTSolver::getProgramBodyString(Program &program) {
  ostringstream output;

  output << "(set-info :smt-lib-version 2.6)" << endl;
  output << "(set-option :produce-models true)" << endl; // TODO don't produce models for performance?
  output << "(set-option :produce-assignments true)" << endl;
  output << "(set-logic ALL)" << endl;

  for (Atom *a : program.atoms) {
    // FIXME Should this declare a const or fun?
    output << "(declare-const " << a->getSmtName() << " Bool)" << endl;
  }

  for (Clause *c : program.clauses) {
    output << "(assert " << c->toSmtLibString() << ")" << endl;
  }

  // TODO declare-fun?
  for (MinimizationStatement *m : program.minimizations) {
    output << "(declare-const " << m->getSmtAtomName() << " Int)" << endl;
    output << "(assert (= " << m->getSmtAtomName() << " (+";
    for (MinimizationAtom *a : m->atoms) {
      output << " (ite " << a->atom.getSmtName() << " " << a->weight << " 0)";
    }
    output << ")))" << endl;
  }

  return output.str();

  // TODO output computeTrue atoms
  // output <<
  // for (Atom* a : program.atoms)
  // {
  // 	if (a->computeTrue)
  // 	{
  // 		output << "(assert " << c->toSmtLibString() << ")" << endl;
  // 	}
  // }

  // output.close();

  // system(string("cat " + outputFileName).c_str());
}
