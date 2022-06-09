#ifndef SMTLOGICS_H_
#define SMTLOGICS_H_


#include <sstream>
#include "program.h"

class ILogic {
public:
  virtual ~ILogic() {};
  virtual string SMT_LOGIC_NAME() = 0;
  virtual void processTheoryStatements(list<TheoryStatement*> statements) = 0;

  virtual void getDeclarationStatements(std::ostringstream &output) = 0;
  virtual void getAssertionStatements(std::ostringstream &output) = 0;
};

class QF_LIA : public ILogic {
public:
    string SMT_LOGIC_NAME() override;
    void processTheoryStatements(list<TheoryStatement*> statements) override;
    void getDeclarationStatements(std::ostringstream &output) override;
    void getAssertionStatements(std::ostringstream &output) override;

private:
    map<int, SymbolicTerm*> symbolicTerms;
    list<TheoryStatement *> statements;

    string toString(TheoryAtomElement* elements);
    string toString(ITheoryTerm* term);
};

#endif // SMTLOGICS_H_
