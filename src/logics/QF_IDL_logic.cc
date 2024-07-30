#include "logic.h"
#include "QF_IDL_logic.h"
#include "glog/logging.h"
#include "program.h"
#include <numeric>
#include "smtstringhelpers.h"

string QF_IDL_logic::SMT_LOGIC_NAME() { return "QF_IDL";}

void QF_IDL_logic::getAssertionStatements(std::ostringstream &output) {
    for (const auto statement : statements) {
        if (statement->symbolicTerm->name == "diff")  {
            list<string> elements;
            for (const auto element : statement->leftElements) {
                elements.push_back(toString(element));
            }
            auto sumOfElements = SMT::Expr("+", elements, true);

            // HACK: SMT-LIB doesn't have a != operator
            string operation = statement->operation->name;
            if (operation == "!=") {
                operation = "distinct";
            }

            auto sumStatement = SMT::Expr(operation, {sumOfElements, SMT::ToString(statement->rightTerm)});

            auto assertion = SMT::Assert(SMT::Expr("=", {SMT::Var(statement->statementAtom), sumStatement}));
            output << assertion;
        }
        else if (statement->symbolicTerm->name == "dom") {
            auto singleElement = statement->leftElements.front();
            auto domainExpression = dynamic_cast<ExpressionTerm*>(singleElement->terms.front());
            NumericTerm* lowerBound = dynamic_cast<NumericTerm*>(domainExpression->children.front());
            NumericTerm* upperBound = dynamic_cast<NumericTerm*>(domainExpression->children.back());

            auto assertion = SMT::Assert(SMT::Expr("<=", {
                    SMT::ToString(lowerBound),
                    SMT::ToString(statement->rightTerm),
                    SMT::ToString(upperBound)
                }));
            output << assertion;
        }
        else {
            LOG(FATAL) << "The " << statement->symbolicTerm->name << " statement is not supported with the logic.";
        }
    }
}