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

class ISymbolicExpression {
public:
  virtual ~ISymbolicExpression() {};
  virtual string ToString() { return ""; };
};

class Symbol : public ISymbolicExpression {
public:
    string content;
    Symbol(string content) {
      this->content = content;
    }

    string ToString() {
      return content;
    }
};

class SymbolList : public ISymbolicExpression {
  public:
    vector<ISymbolicExpression*> children;

    ~SymbolList() {
      for (auto child : children) {
        delete child;
      }
    }

    string ToString() {
      ostringstream output;
      output << "(";
      for (auto child : children) {
        output << child->ToString();
        if (child != children.back()) {
          output << " ";
        }
      }
      output << ")";
      return output.str();
    }
};

// https://stackoverflow.com/questions/15679672/recursive-parsing-for-lisp-like-syntax
class SymbolicExpressionParser {
  public:
    unique_ptr<SymbolList> ParseSymbolList(string input) {
      readTokens(input);
      return unique_ptr<SymbolList>(parseList());
    }
  private:
    list<string> tokens;

    void readTokens(string input) {
      regex r("[()]|[^ ()|]+|\\|[^ ]+\\|");
      smatch match;
      string::const_iterator searchStart(input.cbegin());
      while (regex_search(searchStart, input.cend(), match, r)) {
        searchStart = match.suffix().first;
        tokens.push_back(match[0].str());
      }
    }

    SymbolList* parseList() {
      tokens.pop_front();
      auto list = new SymbolList();
      while (tokens.front() != ")") {
        auto member = parseExpression();
        list->children.push_back(member);
      }
      tokens.pop_front();
      return list;
    }

    ISymbolicExpression* parseExpression() {
      if (tokens.front() == "(") {
        return parseList();
      } else {
        string symbol = tokens.front();
        tokens.pop_front();
        return new Symbol(symbol);
      }
    }
};

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
  // string getCheckSatString(Program &program);
  string getAnswerNegationString(SolverResult& result, bool includeConstraintVariables);
  string getMinimizationAssertionString(map<MinimizationStatement*,string> &minimizationResults);
  void writeToFile(string input, string outputFileName);

  // FIXME
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
