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
#include <cstdlib>
#include <exception>
#include <float.h>
#include <fstream>
#include <glog/logging.h>
#include <iostream>
#include <limits.h>
#include <map>
#include <sstream>
#include <stdexcept>
#include <string.h>
#include <string>

Read::Read(Program *p, Api *a, Param *params) : program(p), api(a), params(params) {
  // atoms = 0;
  size = 0;
  models = 1;
}

Read::~Read() {
  // delete[] atoms;
}

//
// creates an instance of a new atom
//
// FIXME Why do we use Atoms here? This seems like a leak of domain boundaries
// FIXME Why doesn't the API do this check instead?
Atom *Read::getOrCreateAtom(long n) {
  if (atoms[n] == 0)
    atoms[n] = api->new_atom(n);
  return atoms[n];
}

Atom *Read::getAtomFromLiteral(long n) { return getOrCreateAtom(abs(n)); }

int Read::finishReading(FILE *f, long size) {
  long n;
  int count;

  for (long i = 0; i < size; i++) {
    count = fscanf(f, "%ld", &n);
    if (count == EOF || n < 1) {
      cerr << "atom out of bounds, line " << linenumber << endl;
      return 1;
    }
  }
  return 0;
}

// gringo's output used to separate positive and negative portions of the body
int Read::readBody(FILE *f, long size, bool pos, RuleType type) {
  long n;
  int count;
  for (long i = 0; i < size; i++) {
    count = fscanf(f, "%ld", &n);
    //   if (count == EOF || n < 1)
    // {
    //   cerr << "atom out of bounds, line " << linenumber << endl;
    //   return 1;
    // }
    Atom *a = getOrCreateAtom(n);
    // if(!pos)
    //   a->scopeNegAsFail = true;

    // if atom is not added
    // it meens that it is repeated again in the rule
    // and since it is a weight rule we might loose information
    if (type == WEIGHTRULE || type == CONSTRAINTRULE) {
      // a->pbInd.clear();
      // a->nbInd.clear();
      api->add_body(a, pos);
    } else if (!api->add_body_repetition(a, pos, type)) {
      for (i = i + 1; i < size; i++) {
        count = fscanf(f, "%ld", &n);
        // if (count == EOF || n < 1)
        // {
        //   cerr << "atom out of bounds, line " << linenumber << endl;
        //   return 1;
        // }
      }
      // TODO revisit
      api->rule_reset_repetition();
      return -1; // there is no point going this rule father
      // as we can thru this rule away due to same atom in
      // head and pbody for instance or same atom in pos and neg part of the
      // body
    }
  }
  return 0;
}

int Read::addBasicRule(FILE *f) {
  long n;
  int count;
  //  cout<<"BASICRULE"<<endl;
  api->begin_rule(BASICRULE);
  // Rule head
  count = fscanf(f, "%ld", &n);
  // if (count == EOF || n < 1)
  //   {
  //     cerr << "head atom out of bounds, line " << linenumber << endl;
  //     return 1;
  //   }
  Atom *a = getOrCreateAtom(n);
  api->add_head_repetition(a);
  // Body
  count = fscanf(f, "%ld", &n);
  // if (count == EOF || n < 0)
  //   {
  //     cerr << "total body size, line " << linenumber << endl;
  //     return 1;
  //   }
  long body = n;
  // Negative body
  count = fscanf(f, "%ld", &n);

  // if (count == EOF || n < 0 || n > body)
  //   {
  //   cout<<n<<endl;
  //   cout<<body<<endl;
  //     cerr << "negative body size, line " << linenumber << endl;
  //     return 1;
  //   }
  //  cout<<" Reading Negative part "<<endl;
  int retRB = readBody(f, n, false, BASICRULE);
  switch (retRB) {
  case 0:
    break;
  case -1:
    return finishReading(f, body - n);
  case 1:
    return 1;
  }
  //  cout<<" Reading Positive part "<<endl;
  // Positive body
  retRB = readBody(f, body - n, true, BASICRULE);
  switch (retRB) {
  case 0:
    api->end_rule();

    return 0;
  case -1:
    return 0;
  case 1:

    return 1;
  }
}

int Read::addConstraintRule(FILE *f) {
  long n;
  int count;
  api->begin_rule(CONSTRAINTRULE);
  // Rule head
  count = fscanf(f, "%ld", &n);
  if (count == EOF)
    return 1;
  // if (count == EOF || n < 1)
  //   {
  //     cerr << "head atom out of bounds, line " << linenumber << endl;
  //     return 1;
  //   }
  Atom *a = getOrCreateAtom(n);
  api->add_head(a);
  // Body
  count = fscanf(f, "%ld", &n);
  if (count == EOF || n < 0)
    return 1;
  long body = n;
  // Negative body
  count = fscanf(f, "%ld", &n);
  if (count == EOF || n < 0 || n > body)
    return 1;
  long nbody = n;
  // Choose
  count = fscanf(f, "%ld", &n);
  if (count == EOF || n < 0 || n > body)
    return 1;
  api->set_atleast_body(n);
  if (readBody(f, nbody, false, CONSTRAINTRULE) == 1)
    return 1;
  // Positive body
  if (readBody(f, body - nbody, true, CONSTRAINTRULE) == 1)
    return 1;
  api->end_rule();
  return 0;
}

int Read::addGenerateRule(FILE *f) {
  fclose(f);
  cerr << "generate rules are not interpreted by cmodels, line " << linenumber
       << endl;
  return 1;
}

int Read::addChoiceRule(FILE *f) {
  long n;
  int count;
  api->begin_rule(CHOICERULE);
  // Heads
  count = fscanf(f, "%ld", &n);
  // if (count == EOF || n < 1)
  //   {
  //     cerr << "head size less that one, line " << linenumber << endl;
  //     return 1;
  //   }
  long heads = n;
  for (long i = 0; i < heads; i++) {
    count = fscanf(f, "%ld", &n);
    // if (count == EOF || n < 1)
    // {
    //   cerr << "atom out of bounds, line " << linenumber << endl;
    //   return 1;
    // }
    Atom *a = getOrCreateAtom(n);
    api->add_head_repetition(a);
  }

  // Body
  count = fscanf(f, "%ld", &n);
  // if (count == EOF || n < 0)
  //   {
  //     cerr << "total body size, line " << linenumber << endl;
  //     return 1;
  //   }
  long body = n;
  // Negative body
  count = fscanf(f, "%ld", &n);
  if (count == EOF || n < 0 || n > body) {
    cerr << "negative body size, line " << linenumber << endl;
    return 1;
  }
  int retRB = readBody(f, n, false, CHOICERULE);
  switch (retRB) {
  case 0:
    break;
  case -1:
    return finishReading(f, body - n);
  case 1:
    return 1;
  }
  // Positive body
  retRB = readBody(f, body - n, true, CHOICERULE);
  switch (retRB) {
  case 0:
    api->end_rule();
    return 0;
  case -1:
    return 0;
  case 1:
    return 1;
  }
}
int Read::addDisjunctionRule(FILE *f) {
  long n;
  int count;
  api->begin_rule(DISJUNCTIONRULE);
  // Heads
  count = fscanf(f, "%ld", &n);
  if (count == EOF || n < 1) {
    cerr << "head size less than one, line " << linenumber << endl;
    return 1;
  }
  long heads = n;
  for (long i = 0; i < heads; i++) {
    count = fscanf(f, "%ld", &n);
    if (count == EOF || n < 1) {
      cerr << "atom out of bounds, line " << linenumber << endl;
      return 1;
    }
    Atom *a = getOrCreateAtom(n);
    api->add_head_repetition(a);
  }
  // Body
  count = fscanf(f, "%ld", &n);
  if (count == EOF || n < 0) {
    cerr << "total body size, line " << linenumber << endl;
    return 1;
  }
  long body = n;
  // Negative body
  count = fscanf(f, "%ld", &n);
  if (count == EOF || n < 0 || n > body) {
    cerr << "negative body size, line " << linenumber << endl;
    return 1;
  }
  int retRB = readBody(f, n, false, DISJUNCTIONRULE);
  switch (retRB) {
  case 0:
    break;
  case -1:
    return finishReading(f, body - n);
  case 1:
    return 1;
  }
  // Positive body
  retRB = readBody(f, body - n, true, DISJUNCTIONRULE);
  switch (retRB) {
  case 0:
    api->end_rule();
    return 0;
  case -1:
    return 0;
  case 1:
    return 1;
  }
}

int Read::addWeightRule(FILE *f) {
  long n;
  int count;
  // Rule head

  api->begin_rule(WEIGHTRULE);
  // Rule head
  count = fscanf(f, "%ld", &n);
  // if (count == EOF || n < 1)
  //  {
  //     cerr << "head atom out of bounds, line " << linenumber << endl;
  //     return 1;
  //   }
  Atom *a = getOrCreateAtom(n);
  api->add_head(a);
  Weight w;
#ifdef USEDOUBLE
  count = fscanf(f, "%DBL_DIGf", &w);
#else
  count = fscanf(f, "%ld", &w);
#endif

  // Atleast
  // count = fscanf(f,"%DBL_DIGf",&w);
  // f >> w;
  if (count == EOF)
    return 1;
  api->set_atleast_weight(w);
  // Body
  count = fscanf(f, "%ld", &n);
  // if (count == EOF || n < 0)
  //   {
  //     cerr << "Weight rule, total body size, line " << linenumber << endl;
  //     return 1;
  //   }
  long body = n;
  // Negative body
  count = fscanf(f, "%ld", &n);

  // if (count == EOF || n < 0 || n > body)
  //   {
  //     cerr << "Weight rule, negative body size, line " << linenumber << endl;
  //     return 1;
  //   }
  long nbody = n;
  if (readBody(f, nbody, false, WEIGHTRULE))
    return 1;
  // Positive body
  if (readBody(f, body - nbody, true, WEIGHTRULE))
    return 1;
  Weight sum = 0;
  for (long i = 0; i < body; i++) {
#ifdef USEDOUBLE
    count = fscanf(f, "%DBL_DIGf", &w);
#else
    count = fscanf(f, "%ld", &w);
#endif

    if (count == EOF)
      return 1;
    if (sum + w < sum) {
      cerr << "sum of weights in weight rule too large,"
           << " line " << linenumber << endl;
      return 1;
    }
    sum += w;
    if (i < nbody) {

      api->change_body(i, false, w);
    } else {
      api->change_body(i - nbody, true, w);
    }
  }
  api->end_rule();
  return 0;
}

int Read::addOptimizeRule(FILE *f) {
  fclose(f);
  cerr << "Optimize rule are not processed by cmodels, line" << linenumber
       << endl;
  return 1;
}

enum StatementType {
  END = 0,
  RULE = 1,
  MINIMIZE = 2,   // not supported
  PROJECT = 3,    // TODO support later on
  OUTPUT = 4,     // TODO support later on
  EXTERNAL = 5,   // TODO look into later
  ASSUMPTION = 6, // TODO look into later
  HEURISTIC = 7,  // TODO look into later
  EDGE = 8,       // TODO look into later
  THEORY = 9,
  COMMENT = 10
};

enum HeadType {
  // x :- y.
  // x|y :- z.
  DISJUNCTION = 0, // TODO Only support head size 1
  CHOICE = 1       // { x } :- y.
};

enum BodyType { NORMAL_BODY = 0, WEIGHT_BODY = 1 };

// TODO will cmodels support choice head with weight body?

void Read::readRuleLine(istringstream &line) {
  int headType, headLength;
  line >> headType >> headLength;

  if (headType == DISJUNCTION) {
    api->begin_rule(BASICRULE);
  } else if (headType == CHOICE) {
    api->begin_rule(CHOICERULE);
  }

  for (int i = 0; i < headLength; i++) {
    long literal;
    line >> literal;

    Atom *a = getAtomFromLiteral(literal);
    api->add_head_repetition(a);
  }

  if (headLength == 0) {
    Atom *neverAtom = getOrCreateAtom(0);
    neverAtom->name = "never";
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
    throw std::runtime_error("Unsupported body type. Line: " + line.str());
  }

  api->end_rule();
}

void Read::readOutputLine(istringstream &line) {
  int _;
  int numOfLiterals;
  string atomName;
  long atomId;
  line >> _ >> atomName >> numOfLiterals >> atomId;

  // FIXME Include zero numOfLiterals atoms in output
  if (numOfLiterals == 0) {
    auto atom = api->new_atom();
    api->set_name(atom, atomName.c_str());
    api->set_compute(atom, true);
    atom->showInOutputAnswerSet = true;
  } else if (numOfLiterals == 1) {
    Atom *a = getOrCreateAtom(atomId);
    api->set_name(a, atomName.c_str());
    a->showInOutputAnswerSet = true;
  } else if (numOfLiterals > 1) {
    throw std::runtime_error(
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

void Read::readTheoryLine(istringstream &line) {
  int lineType;
  line >> lineType;

  if (lineType == STATEMENT) {
    int atomId;
    line >> atomId;
    Atom *atom = getOrCreateAtom(atomId);
    atom->name = "<theory>";
  }
}

void Read::readMinimizeLine(istringstream &line, int minimizationStatementId) {
  if (params->answerSetsToEnumerate == 1) {
    LOG(WARNING) << "Minimization statements are ignored when only one answer set is generated. Try using the -e flag.";
  }

  int priority, numOfLiterals;
  line >> priority >> numOfLiterals;

  auto minimizationStatement = new MinimizationStatement(minimizationStatementId, priority);

  for (int i = 0; i < numOfLiterals; i++) {
    int literal, weight;
    line >> literal >> weight;
    auto atom = getAtomFromLiteral(literal);
    minimizationStatement->atoms.push_back(new MinimizationAtom(*atom, weight));
  }
  program->minimizations.push_back(minimizationStatement);
}

int Read::read(string fileName) {
  int lineNumber = 0;
  try {
    VLOG(1) << "Opening file: " << fileName;
    ifstream fileStream(fileName);

    string line;
    int minimizationStatementId = 0;
    while (std::getline(fileStream, line)) {
      VLOG(2) << "Reading line: " << line;
      lineNumber++;
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
        readTheoryLine(*lineStream);
        break;
      default:
        LOG(WARNING) << "Encountered unknown statement type: " << statementType
                     << ", skipping.";
        break;
      }
    }

    VLOG(1) << "Done reading";
    return 0;
  } catch (exception e) {
    LOG(FATAL) << "Failed to parse grounded logic program."
               << " Stopped at " << fileName << ":" << lineNumber
               << " Got exception message: " << e.what();
  }
};
