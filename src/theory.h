#ifndef THEORY_H_
#define THEORY_H_

#include "atomrule.h"
#include <functional>
#include <map>
#include <queue>
#include <vector>
#include <sstream>

using namespace std;

class AtomLiteral {
public:
  AtomLiteral(Atom *atom, bool sign) {
    this->atom = atom;
    this->sign = sign;
  }

  Atom *atom;
  bool sign;
};

class ITheoryTerm {
public:
    virtual ~ITheoryTerm() {};

    virtual void traverseNestedTerms(function<void(ITheoryTerm*)> visitor) = 0;
};

class NumericTerm : public ITheoryTerm {
  public:
    int id;
    int value;

    NumericTerm(int id, int value) {
      this->id = id;
      this->value = value;
    }

    void traverseNestedTerms(function<void(ITheoryTerm*)> visitor) override {
      visitor(this);
    }
};

class SymbolicTerm : public ITheoryTerm {
  public:
    int id;
    string name;

    SymbolicTerm(int id, string name) {
      this->id = id;
      this->name = name;
    }

    void traverseNestedTerms(function<void(ITheoryTerm*)> visitor) {
      visitor(this);
    }
};

enum TupleType
{
PARENTHESES = -1,
BRACES = -2,
BRACKETS = -3
};

class TupleTerm : public ITheoryTerm {
  public:
    int id;
    TupleType type;
    list<ITheoryTerm *> children;

    TupleTerm(int id, TupleType type) {
      this->id = id;
      this->type = type;
    }

    void traverseNestedTerms(function<void(ITheoryTerm*)> visitor) {
      visitor(this);
      for (ITheoryTerm* t : children) {
        t->traverseNestedTerms(visitor);
      }
    }
};

class CompoundTerm : public ITheoryTerm {
  public:
    int id;
    SymbolicTerm* operation;
    list<ITheoryTerm *> children;

    CompoundTerm(int id, SymbolicTerm* operation) {
      this->id = id;
      this->operation = operation;
    }

    void traverseNestedTerms(function<void(ITheoryTerm*)> visitor) {
      visitor(this);
      // operation->traverseNestedTerms(visitor);
      for (ITheoryTerm* t : children) {
        t->traverseNestedTerms(visitor);
      }
    }
};


class TheoryAtomElement {
public:
  int id;
  list<ITheoryTerm *> terms;
  list<AtomLiteral> literals;

  TheoryAtomElement(int id) {
    this->id = id;
  }
};

// TODO distinguish operators differently
class TheoryStatement {
public:
  Atom* statementAtom;
  SymbolicTerm* symbolicTerm;
  list<TheoryAtomElement *> leftElements;
  SymbolicTerm* operation;
  ITheoryTerm* rightTerm;

  TheoryStatement(Atom *atom, SymbolicTerm* symbolicTerm, list<TheoryAtomElement *> leftElements, SymbolicTerm* operation, ITheoryTerm *rightTerm) {
    this->statementAtom = atom;
    this->symbolicTerm = symbolicTerm;
    this->leftElements = leftElements;
    this->operation = operation;
    this->rightTerm = rightTerm;
  }
};

#endif // THEORY_H_
