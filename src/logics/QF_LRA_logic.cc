#include "logic.h"
#include "QF_LRA_logic.h"
#include "glog/logging.h"
#include "program.h"
#include <numeric>
#include "smtstringhelpers.h"


string QF_LRA_logic::SMT_LOGIC_NAME() { return "QF_LRA"; }

void QF_LRA_logic::getDeclarationStatements(std::ostringstream &output) {
    for (const auto p : this->symbolicTerms) {
        auto term = p.second;
        output << SMT::DeclareConst(term->name, "Real");
    }
}

void QF_LRA_logic::getAssertionStatements(std::ostringstream &output) {
    for (const auto statement : statements) {
        if (statement->symbolicTerm->name == "sum")  {
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
            RealTerm* lowerBound = dynamic_cast<RealTerm*>(domainExpression->children.front());
            RealTerm* upperBound = dynamic_cast<RealTerm*>(domainExpression->children.back());

            auto assertion = SMT::Assert(SMT::Expr("<=", {
                    SMT::ToString(lowerBound),
                    SMT::ToString(statement->rightTerm),
                    SMT::ToString(upperBound)
                }));
            output << assertion;
        }
        else {
            LOG(FATAL) << "The " << statement->symbolicTerm->name << " statement is not supported with the QF_LRA logic.";
        }
    }
}