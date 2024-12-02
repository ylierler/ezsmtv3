#ifndef QF_LIA_logic_H_
#define QF_LIA_logic_H_


#include <sstream>
#include "program.h"
#include "logic.h"

class QF_LIA_logic : public ILogic {
public:
    string SMT_LOGIC_NAME() override;
    void processTheoryStatements(list<TheoryStatement*> statements) override;
    void getDeclarationStatements(std::ostringstream &output) override;
    void getAssertionStatements(std::ostringstream &output) override;
    list<SymbolicTerm*> getConstraintVariables() override;

    virtual string getSumAssertionStatement(TheoryStatement* statement);
    virtual string getDomAssertionStatement(TheoryStatement* statement);
    string getIndividualOrLowerUpperBoundAssertionStatement(ExpressionTerm* domainExpression, ITheoryTerm* rightTerm);
    string getLowerUpperBoundAssertionStatement(ExpressionTerm* domainExpression, ITheoryTerm* rightTerm);
    string getIndividualUnaryAssertionStatement(ExpressionTerm* domainExpression, ITheoryTerm* rightTerm);
    string getIndividualExpressionAssertionStatement(ExpressionTerm* domainExpression, ITheoryTerm* rightTerm);
    tuple<float, float> getLowerAndUpperBounds(ExpressionTerm* domainExpression);
    float solveExpression(ExpressionTerm* expression);
    float getTermValue(ITheoryTerm* term);

    virtual string getIndividualRealTermExpression(ITheoryTerm* rightTerm, RealTerm* realTerm);
    virtual float getRealTermValue(RealTerm* num);
    virtual string getString(float value);

protected:
    map<int, SymbolicTerm*> symbolicTerms;
    list<TheoryStatement *> statements;

    string toString(TheoryAtomElement* elements);
};

#endif // QF_LIA_logic_H_
