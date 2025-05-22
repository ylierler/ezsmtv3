#include <fstream>
#include "solver/smtprocess.h"
#include "symbolicexpressionparser.h"
#include "smtstringhelpers.h"
#include "utils.h"
#include "boost/process/exception.hpp"

namespace bp = boost::process;
using namespace chrono;

SMTProcess::SMTProcess(SMTSolverCommand type) {
  solverOption = type;

  string solverCommand;
  if (type == CVC4)
    solverCommand =
        "cvc4 --lang smt --output-lang smt --incremental";
  else if (type == CVC5)
    solverCommand =
        "cvc5 --lang smt --output-lang smt --incremental";
  else if (type == Z3)
    solverCommand = "z3 -smt2 -in";
  else if (type == YICES)
    solverCommand = "yices-smt2 --incremental";

  VLOG(3) << "Starting child process for solver: " << solverCommand;
  startChildProcess(solverCommand);
}

SMTProcess::SMTProcess(string customSolverCommand) {
  setSolverOption(customSolverCommand);
  VLOG(3) << "Starting child process for solver: " << customSolverCommand;
  startChildProcess(customSolverCommand);
}

void SMTProcess::startChildProcess(string solverCommand) {
  try {
    process = bp::child(solverCommand, bp::std_out > output, bp::std_in < input);
  }
  catch (bp::process_error& e) {
    string errorMessage = string(e.what()) + 
      "\nError while starting the child process. "
      "Please check if you have " + solvers[solverOption] + " installed.";
    logError(errorMessage);
  }
  catch (...) {
    logError("Error while starting the child process. "
      "Please check if boost library is properly installed.");
  }
}

void SMTProcess::setSolverOption(string solverCommand) {
  transform(solverCommand.begin(), solverCommand.end(), solverCommand.begin(), ::tolower);

  string solver;
  for (string solverName: solvers) {
    transform(solverName.begin(), solverName.end(), solverName.begin(), ::tolower);
    if (solverCommand.find(solverName) != string::npos) {
      solver = solverName;
    }
  }

  if (solver == "cvc4")
    solverOption = CVC4;
  else if (solver == "cvc5")
    solverOption = CVC5;
  else if (solver == "z3")
    solverOption = Z3;
  else if (solver == "yices")
    solverOption = YICES;
}

void SMTProcess::Send(string body) {
  if (VLOG_IS_ON(3)) {
    // Use cout because body might exceed the VLOG() max line length
    cout << "Sending to SMT process: " << body << endl;
  }
  input << body << endl;
}

// convert assignments of answer set to float in real logic 
string prepareDebugAssignmentReal(string str){
  regex re("\\((.*)\\)");
  smatch match;

  std::regex_search(str, match, re);
  string new_string = match[1];

  if (new_string.length() == 0){
    return str;
  }

  vector<string> strs;
  boost::split(strs, new_string, boost::is_any_of(" "));

  if (strs.size() == 3){
    float num = stof(strs[1]) / stof(strs[2]);
    return to_string(num);
  } else {
    return str;
  }
}

// prepare constraints and save to debug file
void prepareDebugFile(Param params, list<string> atomNames, map<string, string> rawAtomAssignments,
                          list<string> variableNames, map<string, string> rawVariableAssignments) {
  ofstream debugFile;
  debugFile.open(params.debugFileName);
  string negatedAssignmentString = "";
  for (auto atomName: atomNames){
    if (rawAtomAssignments[atomName] == "true"){
      negatedAssignmentString += ":- not " + atomName + ".\n";
    }
    else{
      negatedAssignmentString += ":- " + atomName + ".\n";
    }
  }

  for (auto varName: variableNames){
    string varAssignment = rawVariableAssignments[varName];
    if (params.logic == 1){
      varAssignment = "\"" + prepareDebugAssignmentReal(varAssignment) + "\"";
    }
    negatedAssignmentString += "&sum {" + varName + "} = " + varAssignment + ".\n";
  }

  debugFile << negatedAssignmentString;
  debugFile.close();
}

unique_ptr<SolverResult> SMTProcess::CheckSatAndGetAssignments(Program program, list<SymbolicTerm*> &constraintVariables, Param params) {
  auto result = unique_ptr<SolverResult>(new SolverResult());

  auto solveStart = high_resolution_clock::now();
  Send("(check-sat)");
  auto solveEnd = high_resolution_clock::now();
  result->solveDuration = duration_cast<milliseconds>(solveEnd - solveStart);

  string satResult;
  std::getline(output, satResult);
  VLOG(3) << "Read check sat result: " << satResult;
  if (satResult != "unsat" && satResult != "sat") {
    string errorMessage = "Got unexpected result from SMT solver: " + satResult;
    logError(errorMessage);
  }

  if (satResult == "unsat") {
    result->isSatisfiable = false;
    return result;
  }

  result->isSatisfiable = true;

  list<Atom*> answerSetAtoms;
  list<Atom*> allDeclaredAtoms;
  for (auto a : program.atoms) {
    if (a->showInOutputAnswerSet) {
      answerSetAtoms.push_back(a);
    }
    if (!a->isLevelRankingConstraint()) {
      allDeclaredAtoms.push_back(a);
    }
  }

  auto getValuesStart = high_resolution_clock::now();

  // Atoms
  list<string> atomNames;
  transform(allDeclaredAtoms.begin(), allDeclaredAtoms.end(), std::back_inserter(atomNames), [](Atom* a) { return a->getSmtName(); });
  auto rawAtomAssignments = getRawAssignments(atomNames);

  for (Atom* atom : answerSetAtoms) {
    string atomName = atom->getSmtName();
    if (rawAtomAssignments.find(atomName) != rawAtomAssignments.end()) {
      result->atomAssignments[atom] = rawAtomAssignments[atomName] == "true" ? true : false;
    }
  }

  // Constraint variables
  list<string> variableNames;
  transform(constraintVariables.begin(), constraintVariables.end(), std::back_inserter(variableNames), [](SymbolicTerm* t) { return t->name; });
  auto rawVariableAssignments = getRawAssignments(variableNames);

  // check if debug file name is provided
  if (params.debugFileName.length() > 0){
    prepareDebugFile(params, atomNames, rawAtomAssignments, variableNames, rawVariableAssignments);
  }

  for (SymbolicTerm* variable : constraintVariables) {
    if (rawVariableAssignments.find(variable->name) != rawVariableAssignments.end()) {
      result->constraintVariableAssignments[variable] = rawVariableAssignments[variable->name];
    }
  }

  // Minimization statements
  list<string> minimizationAtomNames;
  auto minimizations = program.minimizations;
  transform(minimizations.begin(), minimizations.end(), std::back_inserter(minimizationAtomNames), [](MinimizationStatement* m) { return m->getAtomName(); });
  auto rawMinimizationAssignments = getRawAssignments(minimizationAtomNames);
  for (auto minimization : minimizations) {
    string atomName = minimization->getAtomName();
    if (rawMinimizationAssignments.find(atomName) != rawMinimizationAssignments.end()) {
      result->minimizationAtomAssignments[minimization] = rawMinimizationAssignments[atomName];
    }
  }

  // Roll back to original weights
  for (auto literalWeights: program.lwCollections) {
    int weightsSum = 0;
    for (auto lw: literalWeights){
      int literal = get<0>(lw);
      int weight = get<1>(lw);
      auto a = get<2>(lw);
      
      if (literal > 0 && rawAtomAssignments[a->getSmtName()] == "true") {
        weightsSum += weight;
      }
      else if (literal < 0 && rawAtomAssignments[a->getSmtName()] == "false") {
        weightsSum += weight;
      }
    }
    result->minimizationAtomAssignmentsOriginalWeights.push_back(weightsSum);
  }

  auto getValuesEnd = high_resolution_clock::now();
  result->getValuesDuration = duration_cast<milliseconds>(getValuesEnd - getValuesStart);

  return result;
}

map<string, string> SMTProcess::getRawAssignments(list<string> &variableNames) {
  if (variableNames.empty()) {
    return map<string, string>();
  }

  stringstream getValueStatement;
  getValueStatement << "(get-value (";
  for (string variableName : variableNames) {
    getValueStatement << SMT::VarUnsafe(variableName) << " ";
  }
  getValueStatement << "))";

  Send(getValueStatement.str());

  // Concat multi-line output to single line
  stringstream singleLineStream;
  string line;
  while (std::getline(output, line)) {
    VLOG(3) << "Read line from solver: " << line;
    singleLineStream << line;

    // This is a hacky workaround to handle z3's and yices' multiline output
    size_t lineLength = line.length();
    // if cvc4 or cvc5, break
    if (solverOption == 0 || solverOption == 1) {
      break;
    }
    // if division and negative symbols, check for four closing parenthesis at the end
    else if (line.find("(/") != std::string::npos && line.find("-") != std::string::npos) {
      if (line.substr(lineLength - 4, 4) == "))))") {
        break;
      }
    }
    // if division or negative symbol, check for three closing parenthesis at the end
    else if (line.find("(/") != std::string::npos || line.find("-") != std::string::npos) {
      if (line.substr(lineLength - 3, 3) == ")))") {
        break;
      }
    }
    // if no division or negative symbols, check for two closing parenthesis at the end
    else if (line.substr(lineLength - 2, 2) == "))") {
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

    VLOG(3) << "Parsed assignment: " << SMT::Unescape(variable->content) << "=" << value->ToString();
    rawAssignments[SMT::Unescape(variable->content)] = value->ToString();
  }

  return rawAssignments;
}
