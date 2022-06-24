#ifndef SMTSOLVER_H_
#define SMTSOLVER_H_

#include "boost/process/detail/child_decl.hpp"
#include "boost/process/pipe.hpp"
#include "defines.h"
#include "param.h"
#include "program.h"
#include "smtlogics.h"
#include <boost/process.hpp>
#include <regex>

class ISMTExpression {
public:
  virtual ~ISMTExpression() {};
  virtual string ToString() { return ""; };
};

class SMTVariable : public ISMTExpression {
public:
    string content;
    SMTVariable(string content) {
      this->content = content;
    }

    string ToString() {
      return content;
    }
};

class SMTList : public ISMTExpression {
  public:
    list<ISMTExpression*> children;

    string ToString() {
      ostringstream output;
      output << "(";
      for (auto child : children) {
        output << child->ToString() << " ";
      }
      output << ") ";
      return output.str();
    }
};

// https://stackoverflow.com/questions/15679672/recursive-parsing-for-lisp-like-syntax
class SMTExpressionParser {
  public:
    SMTList* ParseListExpression(string input) {
      readSymbols(input);
      return parseList();
    }
  private:
    list<string> symbols;

    void readSymbols(string input) {
      regex symbolsRegex("[()]|[^ ()]+|\\|[^ ]+\\|");
      smatch match;
      string::const_iterator searchStart(input.cbegin());
      while (regex_search(searchStart, input.cend(), match, symbolsRegex)) {
        cout << "readSymbols " << input;
        searchStart = match.suffix().first;
        symbols.push_back(match[0].str()); // TODO
      }
    }

    SMTList* parseList() {
      symbols.pop_front();
      auto list = new SMTList();
      while (symbols.front() != ")") {
        auto member = parseExpression();
        list->children.push_back(member);
      }
      symbols.pop_front();
      return list;
    }

    ISMTExpression* parseExpression() {
      if (symbols.front() == "(") {
        return parseList();
      } else {
        string symbol = symbols.front();
        symbols.pop_front();
        return new SMTVariable(symbol);
      }
    }
};

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
