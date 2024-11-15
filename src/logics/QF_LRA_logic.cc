#include "logic.h"
#include "QF_LRA_logic.h"
#include "glog/logging.h"
#include "program.h"
#include <numeric>
#include "smtstringhelpers.h"


/*if both types ints and reals are present, return LIRA logic
mixed_logic is true in case of non-tight program, where level ranking variables are integers
typeMap is the map with custom specified types for LIRA logic*/
string QF_LRA_logic::SMT_LOGIC_NAME() {
    if (mixed_logic or typeMap.size()) {
        return "AUFLIRA";
    }
    return "QF_LRA";
}

void QF_LRA_logic::getDeclarationStatements(std::ostringstream &output) {
    for (const auto p : this->symbolicTerms) {
        auto term = p.second;
        string termName = term->name;
        int index = termName.find("(");

        if (index && typeMap.size()) {
            string name = termName.substr(0, index);

            if (typeMap.find(name) != typeMap.end()) {
                string type = typeMap[name];

                if (type == "int") {
                    output << SMT::DeclareConst(termName, "Int");
                    continue;
                }
            }
        }
        output << SMT::DeclareConst(termName, "Real");
    }
}

float QF_LRA_logic::solveExpression(ExpressionTerm* expression) {
    string operation="+";
    float value = 0;

    for (auto child: expression->children) {
        float termValue = 0;

        if (auto num = dynamic_cast<NumericTerm*>(child)) {
            termValue = num->value;
        }
        else if (auto num = dynamic_cast<RealTerm*>(child)) {
            termValue = num->value;
        }
        else if (auto expression = dynamic_cast<ExpressionTerm*>(child)) {
            termValue = solveExpression(expression);
        }

        // Apply the operation
        if (operation == "+") {
            value += termValue;
        } 
        else if (operation == "-") {
            value -= termValue;
        } 
        else if (operation == "*") {
            value *= termValue;
        }

        // Update operation for next term
        operation = expression->operation->name;
    }
    return value;
}

float QF_LRA_logic::getTermValue(ITheoryTerm* term) {
    if (auto num = dynamic_cast<NumericTerm*>(term)) {
        return static_cast<float>(num->value);
    }
    if (auto num = dynamic_cast<RealTerm*>(term)) {
        return num->value;
    }
    else if (auto exp = dynamic_cast<ExpressionTerm*>(term)) {
        return solveExpression(exp);
    }
    LOG(FATAL) << "Invalid syntax for dom statement." << endl;
}

tuple<float, float> QF_LRA_logic::getLowerAndUpperBounds(ExpressionTerm* domainExpression) {
    ITheoryTerm* lbTerm = domainExpression->children.front();
    ITheoryTerm* ubTerm = domainExpression->children.back();
        
    float lowerBound = getTermValue(lbTerm);
    float upperBound = getTermValue(ubTerm);
    cout << lowerBound << " " << upperBound << endl;
    return make_tuple(lowerBound, upperBound);
}

string QF_LRA_logic::getUnaryOrLowerUpperBoundAssertionStatements(ExpressionTerm* domainExpression, ITheoryTerm* rightTerm) {
    // check for unary values 
    if (
        domainExpression->children.size() == 1
        && domainExpression->operation->name == "-"
    )
    {
        float value;

        if (auto num = dynamic_cast<NumericTerm*>(domainExpression->children.front())) {
            value = static_cast<float>(num->value);
        }
        else if (auto num = dynamic_cast<RealTerm*>(domainExpression->children.front())) {
            value = num->value;
        }
        else {
            LOG(FATAL) << "Invalid syntax for unary value." << endl;
        }

        string expression = " " + SMT::Expr("=", {
            SMT::ToString(rightTerm),
            "(- " + to_string(value) + ")"
        });

        return expression;
    }

    // for .. operation with lower-bound and upper-bound
    else {
        auto boundTuple = getLowerAndUpperBounds(domainExpression);
        float lowerBound = get<0>(boundTuple);
        float upperBound = get<1>(boundTuple);

        string expression = " " + SMT::Expr("<=", {
            to_string(lowerBound),
            SMT::ToString(rightTerm),
            to_string(upperBound)
        });

        return expression;
    }
}

void QF_LRA_logic::getAssertionStatements(std::ostringstream &output) {
    for (const auto statement : statements) {
        string assertion;

        if (statement->symbolicTerm->name == "sum")  {
            assertion = getSumAssertionStatement(statement);
        }
        
        else if (statement->symbolicTerm->name == "dom") {
            string expression = "or";
            for (auto singleElement: statement->leftElements){
                // for expression term with unary values, and lower-bound and upper-bound inside dom
                if (dynamic_cast<ExpressionTerm*>(singleElement->terms.front())) {
                    auto domainExpression = dynamic_cast<ExpressionTerm*>(singleElement->terms.front());
                    expression += getUnaryOrLowerUpperBoundAssertionStatements(domainExpression, statement->rightTerm);
                }

                // for individual integer values inside dom
                else if (auto numericTerm = dynamic_cast<NumericTerm*>(singleElement->terms.front())) {
                    expression += " " + SMT::Expr("=", {
                        SMT::ToString(statement->rightTerm),
                        SMT::ToString(numericTerm)
                    });
                }

                // for individual real values inside dom
                else if (auto realTerm = dynamic_cast<RealTerm*>(singleElement->terms.front())) {
                    expression += " " + SMT::Expr("=", {
                        SMT::ToString(statement->rightTerm),
                        SMT::ToString(realTerm)
                    });
                }
            }
            expression = "(" + expression + ")";
            assertion = SMT::Assert(expression);
        }

        else {
            LOG(FATAL) << "The " << statement->symbolicTerm->name << " statement is not supported with the " << SMT_LOGIC_NAME() << " logic.";
        }

        output << assertion;
    }
}
