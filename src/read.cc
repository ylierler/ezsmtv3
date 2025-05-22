/*
 * File read.cc
 * Last modified on 2 19:34 2002
 * By Yuliya Babovich
 *
 */

// Copyright 1998 by Patrik Simons
// This program is free software; you can redistribute it and/or
// modify it under the terms of the GNU General Public License
// as published by the Free Software Foundation; either version 2
// of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place - Suite 330, Boston,
// MA 02111-1307, USA.
//
// Patrik.Simons@hut.fi
#include "read.h"
#include "atomrule.h"
#include "defines.h"
#include "program.h"
#include "theory.h"
#include <cstdlib>
#include <exception>
#include <float.h>
#include <fstream>
#include <glog/logging.h>
#include <iostream>
#include <limits.h>
#include <list>
#include <map>
#include <numeric>
#include <regex>
#include <sstream>
#include <stdexcept>
#include <string.h>
#include <string>
#include <boost/algorithm/string.hpp>
#include "utils.h"

using namespace boost::algorithm;

Read::Read(Program *p, Api *a, Param *params) : program(p), api(a), params(params) {
  // atoms = 0;
  size = 0;
  models = 1;
  mValues[-1] = 1;
}

//
// creates an instance of a new atom
//
// FIXME Why doesn't the API do this check instead?
Atom *Read::getOrCreateAtom(long n) {
  if (atoms[n] == 0)
    atoms[n] = api->new_atom(n);
  return atoms[n];
}

Atom *Read::getAtomFromLiteral(long n) { return getOrCreateAtom(abs(n)); }

enum StatementType {
  END = 0,
  RULE = 1,
  MINIMIZE = 2,
  PROJECT = 3,    // NOTE Not supported
  OUTPUT = 4,
  EXTERNAL = 5,   // NOTE Not supported
  ASSUMPTION = 6, // NOTE Not supported
  HEURISTIC = 7,  // NOTE Not supported
  EDGE = 8,       // NOTE Not supported
  THEORY = 9,
  COMMENT = 10
};

enum HeadType {
  // x :- y.
  // x|y :- z.
  DISJUNCTION = 0,
  // { x } :- y.
  CHOICE = 1
};

enum BodyType { NORMAL_BODY = 0, WEIGHT_BODY = 1 };

void Read::readRuleLine(istringstream &line) {
  int headType, headLength;
  line >> headType >> headLength;

  if (headType == DISJUNCTION) {
    api->begin_rule(BASICRULE);
  } else if (headType == CHOICE) {
    api->begin_rule(CHOICERULE);
  }

  if (headType == DISJUNCTION && headLength > 1) {
    string errorMessage = "Disjunction rules with more than one head atom are not supported. Line: " + line.str();
    logError(errorMessage);
  }

  for (int i = 0; i < headLength; i++) {
    long literal;
    line >> literal;

    Atom *a = getAtomFromLiteral(literal);
    api->add_head_repetition(a);
  }

  if (headLength == 0) {
    Atom *neverAtom = getOrCreateAtom(0);
    api->set_name(neverAtom, NEVER_ATOM.c_str());
    api->set_compute(neverAtom, false);

    program->false_atom = neverAtom;

    api->add_head_repetition(neverAtom);

    // FIXME setting type to constraint rule seems to break things
    // api->type = CONSTRAINTRULE;
  }

  int bodyType;
  line >> bodyType;

  if (bodyType == NORMAL_BODY) {
    int bodyLength;
    line >> bodyLength;
    for (int i = 0; i < bodyLength; i++) {
      long literal;
      line >> literal;

      Atom *a = getAtomFromLiteral(literal);

      // FIXME How important is the repetition variant?
      // Shouldn't gringo handle this?
      api->add_body(a, literal > 0);
      // api->add_body_repetition(a, literal > 0, api->type);
    }
  } else if (bodyType == WEIGHT_BODY) {
    Weight lowerBound;
    int numOfLiterals;
    line >> lowerBound >> numOfLiterals;

    api->type = WEIGHTRULE;
    api->set_atleast_weight(lowerBound);

    for (int i = 0; i < numOfLiterals; i++) {
      long literal;
      Weight weight;
      line >> literal >> weight;

      Atom *a = getAtomFromLiteral(literal);
      api->add_body(a, literal > 0, weight);
    }
  } else {
    throw runtime_error("Unsupported body type. Line: " + line.str());
  }

  api->end_rule();
}

void Read::readOutputLine(istringstream &line) {
  int _;
  int numOfLiterals;
  string atomName;
  long atomId;
  line >> _ >> atomName >> numOfLiterals >> atomId;

  if (numOfLiterals == 0) {
    auto atom = api->new_atom();
    api->set_name(atom, atomName.c_str());
    api->set_compute(atom, true);
    atom->showInOutputAnswerSet = true;

    api->begin_rule(BASICRULE);
    api->add_head(atom);
    api->end_rule();

  } else if (numOfLiterals == 1) {
    Atom *a = getOrCreateAtom(atomId);
    api->set_name(a, atomName.c_str());
    a->showInOutputAnswerSet = true;
  } else if (numOfLiterals > 1) {
    throw runtime_error(
        "Output line with multiple literals not implemented yet. Line: " +
        line.str());
  }
}

enum TheoryLineType {
  NUMERIC_TERMS = 0,
  SYMBOLIC_TERMS = 1,
  COMPOUND_TERMS = 2,
  ATOM_ELEMENTS = 4,
  DIRECTIVE = 5,
  STATEMENT = 6
};

// TODO support directives
void Read::readTheoryStatements(list<string> &lines) {
  for (string line : lines) {
    stringstream lineStream(line);
    int statementType, theoryLineType;
    lineStream >> statementType;

    if (statementType == THEORY) {
      lineStream >> theoryLineType;

      if (theoryLineType == STATEMENT) {
        int atomId;
        lineStream >> atomId;
        Atom *atom = getOrCreateAtom(atomId);
        atom->theoryStatement = true;

        // treat all theory statement atoms as a choice rule atom
        string choiceRuleLine = "1 1 " + to_string(atomId) + " 0 0";
        unique_ptr<istringstream> choiceRulelineStream(new istringstream(choiceRuleLine));
        readRuleLine(*choiceRulelineStream);

        stringstream name;
        name << THEORY_ATOM_PREFIX << "(" << atomId << ")";
        api->set_name(atom, name.str().c_str());

        int symbolicTermId;
        lineStream >> symbolicTermId;
        auto symbolicTerm = dynamic_cast<SymbolicTerm*>(program->theoryTerms[symbolicTermId]);
        if (symbolicTerm == nullptr) {
          string errorMessage = "Could not find symbolic theory term " + to_string(symbolicTermId) + " referenced by line '" + line + "'";
          logError(errorMessage);
        }

        int numOfElements;
        lineStream >> numOfElements;
        list<TheoryAtomElement *> leftElements;
        for (int i = 0; i < numOfElements; i++) {
          int theoryAtomElementId;
          lineStream >> theoryAtomElementId;
          auto element = program->theoryAtomElements[theoryAtomElementId];
          if (element == nullptr) {
            string errorMessage = "Could not find theory atom element " + to_string(theoryAtomElementId) + " referenced by line '" + line + "'";
            logError(errorMessage);
          }
          leftElements.push_back(element);
        }

        int operatorTermId;
        lineStream >> operatorTermId;
        auto operatorTerm = dynamic_cast<SymbolicTerm*>(program->theoryTerms[operatorTermId]);
        if (operatorTerm == nullptr) {
          string errorMessage = "Could not find operator theory term " + to_string(operatorTermId) + " referenced by line '" + line + "'";
          logError(errorMessage);
        }

        int rightTermId;
        lineStream >> rightTermId;
        auto rightTerm = program->theoryTerms[rightTermId];
        if (rightTerm == nullptr) {
          string errorMessage = "Could not find right theory term " + to_string(rightTermId) + " referenced by line '" + line + "'";
          logError(errorMessage);
        }

        // for type specification statements
        if (symbolicTerm->name == "type") {
          if (params->logic == 2) {
            saveTypes(leftElements, rightTerm);
          }
          else {
            LOG(WARNING) << "LIRA logic required for type specification!! Ignoring type specifications..." << endl;
          }
          continue;
        }

        auto statement = new TheoryStatement(atom, symbolicTerm, leftElements, operatorTerm, rightTerm);
        program->theoryStatements[atomId] = statement;
      }
    }
  }
}

void Read::saveTypes(list<TheoryAtomElement*> leftElements, ITheoryTerm* rightTerm) {
  string variableType;
  if (auto type = dynamic_cast<SymbolicTerm*>(rightTerm)){
    variableType = type->name;
    transform(variableType.begin(), variableType.end(), variableType.begin(), ::tolower);
    if (variableType != "int" && variableType != "real") {
      logError("Invalid variable type. Only 'int' and 'real' are allowed.");
    }
  }
  else {
    logError("Only variables types such as 'int' and 'real' are allowed for type specifications.");
  }

  for (auto element: leftElements) {
    if (element->terms.size() > 1) {
      logError("Please use ';' instead of ',' to separate variables in type specifications.");
    }
    
    auto term = element->terms.front();
    if (auto variable = dynamic_cast<SymbolicTerm*>(term)) {
      program->typeMap[variable->name] = variableType;
    }
    else {
      logError("Only variable names are allowed inside type specifications.");
    }
  }
}

void Read::readTheoryTerms(list<string> &lines) {
  for (string line : lines) {
    stringstream lineStream(line);
    int statementType;
    lineStream >> statementType;

    if (statementType == THEORY) {
      int theoryLineType, termId;
      lineStream >> theoryLineType >> termId;

      switch (theoryLineType) {
        case NUMERIC_TERMS:
          int termValue;
          lineStream >> termValue;
          program->theoryTerms[termId] = new NumericTerm(termId, termValue);
          break;

        case SYMBOLIC_TERMS: {
          int length;
          string symbolValue;
          lineStream >> length >> symbolValue;
          
          // check for quotes around a symbolic term
          if (((!symbolValue.empty() && symbolValue.front() == '"' && symbolValue.back() == '"') ||
              (!symbolValue.empty() && symbolValue.front() == '\'' && symbolValue.back() == '\'')))
          { 
            // try the conversion of the symbolic term from string to float
            try {
              string floatString = trim_copy_if(symbolValue, is_any_of("\"\'"));
              float floatValue = stof(floatString);

              // if LRA or LIRA, use the converted float value
              if (params->logic == 1 || params->logic == 2) {
                program->theoryTerms[termId] = new RealTerm(termId, floatValue);
              }
              // else print a warning message and use it as a symbolic term
              else {
                string warningMessage = "Real number with quotes detected in the program. " + symbolValue +
                  "\nPlease use command line option -l (1|2) to run it in a Real Logic setting." + 
                  "\nFor usage information: ezsmt -h";
                LOG(WARNING) << warningMessage;
                program->theoryTerms[termId] = new SymbolicTerm(termId, symbolValue);
              }
            }
            catch (...) {
              program->theoryTerms[termId] = new SymbolicTerm(termId, symbolValue);
            }
          }
          else {
            program->theoryTerms[termId] = new SymbolicTerm(termId, symbolValue);
          }

          break;
        }

        case COMPOUND_TERMS:
          int t, numOfTerms;
          lineStream >> t >> numOfTerms;

          if (t < 0) {
            auto tupleTerm = new TupleTerm(termId, (TupleType)t);
            for (int i = 0; i < numOfTerms; i++) {
              int childTermId;
              lineStream >> childTermId;
              auto childTerm = program->theoryTerms[childTermId];

              if (childTerm == nullptr) {
                string errorMessage = "Could not find child theory term " + to_string(childTermId) + " referenced by line '" + line + "'";
                logError(errorMessage);
              }

              tupleTerm->children.push_back(childTerm);
            }
            program->theoryTerms[termId] = tupleTerm;
          } 
          else {
            auto operationTerm = dynamic_cast<SymbolicTerm*>(program->theoryTerms[t]);
            if (operationTerm == nullptr) {
              string errorMessage = "Could not find symbolic operator theory term \"" + operationTerm->name + "\" referenced by line '" + line + "'";
              logError(errorMessage);
            }

            list<ITheoryTerm*> childTerms;
            for (int i = 0; i < numOfTerms; i++) {
              int childTermId;
              lineStream >> childTermId;
              auto childTerm = program->theoryTerms[childTermId];
              if (childTerm == nullptr) {
                string errorMessage = "Could not find child theory term " + to_string(childTermId) + " referenced by line '" + line + "'";
                logError(errorMessage);
              }
              childTerms.push_back(childTerm);
            }

            ITheoryTerm* newTerm;

            bool isValidSymbolName = regex_match(operationTerm->name, regex("^[A-z_]+$"));
            if (isValidSymbolName) {
              ostringstream symbolName;
              symbolName << operationTerm->name;
              symbolName << "(";
              int length = 0;
              int childTermsLength = childTerms.size();
              for (auto child : childTerms) {
                if (auto symbolicTerm = dynamic_cast<SymbolicTerm*>(child)) {
                  symbolName << symbolicTerm->name;
                } 
                else if (auto numericTerm = dynamic_cast<NumericTerm*>(child)) {
                  symbolName << numericTerm->value;
                } 
                else {
                  string errorMessage = "Constraint variables can only contain numeric or symbolic terms. Line: " + line;
                  logError(errorMessage);
                }

                if (length < childTermsLength - 1) {
                  symbolName << ",";
                  length += 1;
                }
              }
              symbolName << ")";
              newTerm = new SymbolicTerm(termId, symbolName.str());
            } else {
              auto expressionTerm = new ExpressionTerm(termId, operationTerm);
              expressionTerm->children = childTerms;
              newTerm = expressionTerm;
            }

            program->theoryTerms[termId] = newTerm;
          }
          break;
      }
    }
  }
}

void Read::readTheoryAtomElements(list<string> &lines) {
  for (string line : lines) {
    stringstream lineStream(line);
    int statementType;
    lineStream >> statementType;

    if (statementType == THEORY) {
      int theoryLineType, theoryAtomElementId;
      lineStream >> theoryLineType >> theoryAtomElementId;

      if (theoryLineType == ATOM_ELEMENTS) {
        auto theoryAtomElements = new TheoryAtomElement(theoryAtomElementId);

        int numOfTerms;
        lineStream >> numOfTerms;
        for (int i = 0; i < numOfTerms; i++) {
          int termId;
          lineStream >> termId;
          auto theoryTerm = program->theoryTerms[termId];
          if (theoryTerm == nullptr) {
            string errorMessage = "Could not find definition for theory term " + to_string(termId) + " referenced in '" + line + "'";
            logError(errorMessage);
          }

          theoryAtomElements->terms.push_back(theoryTerm);
        }

        int numOfLiterals;
        lineStream >> numOfLiterals;
        for (int i = 0; i < numOfLiterals; i++) {
          int literal;
          lineStream >> literal;
          int atomId = abs(literal);
          auto atom = atoms[atomId];
          if (atom == nullptr) {
            string errorMessage = "Could not find definition for atom " + to_string(atomId) + " referenced in '" + line + "'";
            logError(errorMessage);
          }

          theoryAtomElements->literals.push_back(AtomLiteral(atom, literal >= 0));
        }

        program->theoryAtomElements[theoryAtomElementId] = theoryAtomElements;
      }
    }
  }
}

void Read::readMinimizeLine(istringstream &line, int minimizationStatementId) {
  params->answerSetsToEnumerate = 0;
  params->includeConstraintsInEnumeration = true;
  params->optimization = true;

  int priority, numOfLiterals;
  line >> priority >> numOfLiterals;

  int literal, weight;
  list<int> weights;
  list<tuple<int, int, Atom*>> literalWeights;
  for (int i = 0; i < numOfLiterals; i++) {
    line >> literal >> weight;

    // drop literal if weight is 0
    if (weight == 0) {
      continue;
    }

    weights.push_back(weight);
    Atom *a = getAtomFromLiteral(literal);
    tuple<int, int, Atom*> lw(literal, weight, a);
    literalWeights.push_back(lw);
  }

  program->lwCollections.push_front(literalWeights);

  // calculate sum of absolute weights for a priority level
  int weightsSum = 0;
  for (int weight: weights) {
    weightsSum += weight < 0 ? -1*weight : weight;
  }

  mValues[priority] = 1 + weightsSum;

  fValues[priority] = 1;
  for (auto m: mValues) {
    if (m.first < priority) {
      fValues[priority] *= m.second;
    } 
  }
  
  int normalized_priority = 0;
  auto minimizationStatement = new MinimizationStatement(minimizationStatementId, normalized_priority);
  size_t len_minimizations = program->minimizations.size();
  
  if (len_minimizations > 0) {
    minimizationStatement = program->minimizations.front();
  }

  for (auto lw: literalWeights) {
    literal = get<0>(lw);
    weight = get<1>(lw) * fValues[priority];

    // weight and literal conversion if negative weight
    if (weight < 0) {
      weight = -1 * weight;
      literal = -1 * literal;
    }

    auto atom = getAtomFromLiteral(literal);
    minimizationStatement->atoms.push_back(new MinimizationAtom(*atom, weight, literal < 0));
  }

  if (len_minimizations <= 0) {
    program->minimizations.push_back(minimizationStatement);
  }
}

int Read::read(string fileName) {
  int lineNumber = 0;
  list<string> lines;

  try {
    VLOG(2) << "Opening file: " << fileName;
    ifstream fileStream(fileName);

    string line;
    int minimizationStatementId = 0;
    while (getline(fileStream, line)) {
      VLOG(3) << "Reading line: " << line;
      lineNumber++;
      lines.push_back(line);
      unique_ptr<istringstream> lineStream(new istringstream(line));

      int statementType;
      *lineStream >> statementType;

      switch (statementType) {
      case COMMENT:
      case END:
        break;
      case RULE:
        readRuleLine(*lineStream);
        break;
      case MINIMIZE:
        readMinimizeLine(*lineStream, minimizationStatementId);
        minimizationStatementId++;
        break;
      case OUTPUT:
        readOutputLine(*lineStream);
        break;
      case THEORY:
        // Handled out of sequence below
        break;
      default:
        LOG(WARNING) << "Encountered unknown statement type: " << statementType
                     << ", skipping.";
        break;
      }
    }
  } catch (exception e) {
    std::string errorMessage = "Failed to parse grounded logic program."
                " Stopped at " + fileName + ":" + std::to_string(lineNumber) +
                ". Got exception message: " + e.what();
    logError(errorMessage);
  }

  VLOG(2) << "Reading theory components";

  readTheoryTerms(lines);
  readTheoryAtomElements(lines);
  readTheoryStatements(lines);

  VLOG(2) << "Done reading";

  deleteFile(fileName);
  return 0;
};
