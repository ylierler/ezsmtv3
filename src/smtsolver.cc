#include "smtsolver.h"
#include "timer.h"
#include <boost/process.hpp>
#include <cstring>
#include <fstream>
#include <glog/logging.h>
#include <iostream>
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
        "../tools/cvc4 --lang smt --output-lang smtlib2.6 --incremental";
  else if (params.SMTsolver == Z3)
    solverCommand = "../tools/z3-4.8.17 -smt2 -in";
  else if (params.SMTsolver == YICES)
    solverCommand = "../tools/yices-smt2 ";

  // Override -s option with --solver-command if provided
  if (!params.smtSolverCommand.empty()) {
    solverCommand = params.smtSolverCommand;
  }

  stringstream ss;

  string smtFileName = "output.smt";

  string programBody = getProgramBodyString(program);
  string programCheckSatFooter = getCheckSatString(program);

  bp::ipstream solverOutput;
  bp::opstream solverInput;

  VLOG(1) << "Starting child process for solver: " << solverCommand;
  bp::child solverProcess(solverCommand, bp::std_out > solverOutput,
                          bp::std_in < solverInput);

  solverInput << programBody;
  if (VLOG_IS_ON(2)) {
    cout << "Wrote program body:" << endl << programBody;
  }

  int i = 1;
  for (;; i++) {
    VLOG(1) << "SMT solver, iteration " << i;
    Timer timer;
    timer.start();

    solverInput << programCheckSatFooter << endl;
    VLOG(2) << "Wrote check sat footer:" << endl << programCheckSatFooter;

    vector<string> resultAnswerSets;
    bool isSatisfiable = parseSolverResults(solverOutput, resultAnswerSets);

    if (!isSatisfiable) {
      break;
    }

    if (params.answerSetsToEnumerate != 1) {
      cout << "Answer set " << i << ": ";
    }

    for (auto smtAtom : resultAnswerSets) {
      cout << smtAtom.substr(1, smtAtom.size() - 2) << " ";
    }
    cout << endl;

    auto answerSetNegation = getAnswerSetNegationString(resultAnswerSets);

    solverInput << answerSetNegation;

    timer.stop();
    VLOG(1) << "Finished round " << i << " in " << timer.sec << "s "
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

  VLOG(2) << "Wrote SMT-LIB file:" << endl << input << endl;
}

bool SMTSolver::parseSolverResults(bp::ipstream &inputStream,
                                   vector<string> &resultAnswerSet) {
  string satResult;
  std::getline(inputStream, satResult);
  VLOG(1) << "Read check sat result: " << satResult;
  if (satResult != "unsat" && satResult != "sat") {
    LOG(FATAL) << "Got unexpected result from SMT solver: " << satResult;
  }

  if (satResult == "unsat") {
    return false;
  }

  stringstream atomsListStream;
  string line;
  while (std::getline(inputStream, line)) {
    VLOG(1) << "Read line from solver: " << line;
    atomsListStream << line;

    // TODO This is a hacky workaround for z3's multiline output
    if (line[line.length() - 2] == ')' && line[line.length() - 1] == ')') {
      break;
    }
  }
  string atomsList = atomsListStream.str();

  regex r("\\((\\|[^ ]*\\|) true\\)");
  smatch match;
  string::const_iterator searchStart(atomsList.cbegin());
  while (regex_search(searchStart, atomsList.cend(), match, r)) {
    searchStart = match.suffix().first;
    resultAnswerSet.push_back(match[1].str());
  }

  return true;
}

string SMTSolver::getAnswerSetNegationString(vector<string> &answerSet) {
  // TODO Should I include negatives (false)?

  ostringstream output;
  output << "(push 1)" << endl;
  output << "(assert (not (and";
  for (string smtAtom : answerSet) {
    output << " " << smtAtom;
  }
  output << ")))" << endl;

  VLOG(2) << "Generated answer set negation:" << endl << output.str();
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
  output << "))" << endl;

  return output.str();
}

// FIXME this is copying strings
string SMTSolver::getProgramBodyString(Program &program) {
  ostringstream output;

  output << "(set-info :smt-lib-version 2.6)" << endl;
  output << "(set-option :produce-models true)" << endl;
  output << "(set-option :produce-assignments true)" << endl;
  output << "(set-logic ALL)" << endl;

  for (Atom *a : program.atoms) {
    // FIXME Should this declare a const or fun?
    output << "(declare-fun " << a->getSmtName() << " () Bool)" << endl;
  }

  for (Clause *c : program.clauses) {
    output << "(assert " << c->toSmtLibString() << ")" << endl;
  }

  // TODO
  for (MinimizationStatement *m : program.minimizations) {
    output << "(minimize (+";
    for (MinimizationAtom *a : m->atoms) {
      output << " (ite " << a->atom.getSmtName() << " " << a->weight << " 0)";
    }
    output << "))" << endl;
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
