#include "logic.h"
#include "QF_IDL_logic.h"
#include "glog/logging.h"
#include "program.h"
#include <numeric>
#include "smtstringhelpers.h"
#include "utils.h"

string QF_IDL_logic::SMT_LOGIC_NAME() {
    if (optimization) {
        VLOG(1) << "IDL logic with optimization is converted to LIA logic."
            "\nUsing LIA logic" << endl;
        return "QF_LIA";
    }
    return "QF_IDL";
}

string QF_IDL_logic::getDiffAssertionStatement(TheoryStatement* statement) {
    if (statement->leftElements.size() > 1) {
        logError("Invalid syntax for diff statment. More than one difference expression is not allowed.");
    }

    auto element = statement->leftElements.front();
    auto term = element->terms.front();

    // lambda counter function for recursion on counting symbolic terms (variables) within nested expression terms
    std::function<void(ExpressionTerm*, int&)> countVariables = [&](ExpressionTerm* expressionTerm, int& count) {
        for (auto child: expressionTerm->children) {
            if (auto nestedExpression = dynamic_cast<ExpressionTerm*>(child)) {
                countVariables(nestedExpression, count);
            }
            else if (auto symbolicTerm = dynamic_cast<SymbolicTerm*>(child)) {
                if (++count > 2) {
                    logError("Invalid syntax for diff statment. More than two variables are not allowed in a difference expression.");
                }
            }
        }
    };

    int variableCount = 0;
    // check if there are more than two variables in difference expression
    if (auto expressionTerm = dynamic_cast<ExpressionTerm*>(term)) {
        countVariables(expressionTerm, variableCount);  

        if (expressionTerm->operation->name != "-") {
            logError("Invalid syntax for diff statment. Only difference operation is allowed.");
        }
    }

    if ((variableCount == 2) && (!dynamic_cast<NumericTerm*>(statement->rightTerm))) {
        logError("Right term can only be an integer when there are already two variables in the difference expression.");
    }

    string operation = statement->operation->name;
    auto diffStatement = SMT::Expr(operation, {toString(element), SMT::ToString(statement->rightTerm)});
    return diffStatement;
}

void QF_IDL_logic::getAssertionStatements(std::ostringstream &output) {
    for (const auto statement : statements) {
        string assertionStatement;
        if (statement->symbolicTerm->name == "diff")  {
            assertionStatement = getDiffAssertionStatement(statement);
        }
        else if (statement->symbolicTerm->name == "dom") {
            assertionStatement = getDomAssertionStatement(statement);
        }
        else {
            string errorMessage = "The " + statement->symbolicTerm->name + " statement is not supported with the " + SMT_LOGIC_NAME() + " logic.";
            logError(errorMessage);
        }

        string assertion = SMT::Assert(SMT::Expr("=", {SMT::Var(statement->statementAtom), assertionStatement}));
        output << assertion;
    }
}