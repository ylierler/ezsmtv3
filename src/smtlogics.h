#ifndef SMTLOGICS_H_
#define SMTLOGICS_H_


#include <sstream>
#include "program.h"

class ILogic {
public:
  virtual ~ILogic() {};
  virtual string SMT_LOGIC_NAME() = 0;
  virtual void processTheoryStatement(TheoryStatement *statement) = 0;

  virtual void getDeclarationStatements(std::ostringstream &output) = 0;
  virtual void getAssertionStatements(std::ostringstream &output) = 0;
};

class QF_LIA : public ILogic {
public:
    string SMT_LOGIC_NAME() override;
    void processTheoryStatement(TheoryStatement *statement) override;
    void getDeclarationStatements(std::ostringstream &output) override;
    void getAssertionStatements(std::ostringstream &output) override;

private:
    map<int, SymbolicTerm*> symbolicTerms;
    list<TheoryStatement *> statements;

    string toString(TheoryAtomElement* elements);
    string toString(ITheoryTerm* term);
};

#endif // SMTLOGICS_H_
