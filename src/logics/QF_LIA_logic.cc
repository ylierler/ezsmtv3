#include "logic.h"
#include "QF_LIA_logic.h"
#include "glog/logging.h"
#include "program.h"
#include <numeric>
#include "smtstringhelpers.h"

string QF_LIA_logic::SMT_LOGIC_NAME() { return "QF_LIA"; }

void QF_LIA_logic::processTheoryStatements(list<TheoryStatement*> statements) {
    this->statements = statements;

    for (auto statement : statements) {
        statement->traverseNestedTerms([&](ITheoryTerm* term) {
            if (auto s = dynamic_cast<SymbolicTerm*>(term)) {
                this->symbolicTerms[s->id] = s;
            }
            else if (auto s = dynamic_cast<ExpressionTerm*>(term)) {
                for (auto childTerm: s->children){
                    if (auto child = dynamic_cast<SymbolicTerm*>(childTerm)) {
                        this->symbolicTerms[child->id] = child;
                    }
                }
            }
        });
    }
}

void QF_LIA_logic::getDeclarationStatements(std::ostringstream &output) {
    for (const auto p : this->symbolicTerms) {
        auto term = p.second;
        output << SMT::DeclareConst(term->name, "Int");
    }
}

// fix for unary symbols and boundValue=0 for multiplication
int getValue(ExpressionTerm* expression, int boundValue=0, string operation="+") {
    for (auto child: expression->children) {
        if (dynamic_cast<NumericTerm*>(child)) {
            NumericTerm* num = dynamic_cast<NumericTerm*>(child);
            if (operation == "+") {
                boundValue += num->value;
            }
            else if (operation == "-") {
                boundValue -= num->value;
            }
            else if (operation == "*") {
                boundValue *= num->value;
            }
        }
        else if (dynamic_cast<ExpressionTerm*>(child)) {
            ExpressionTerm* expression = dynamic_cast<ExpressionTerm*>(child);
            int expressionBoundValue = getValue(expression);
            if (operation == "+") {
                boundValue += expressionBoundValue;
            }
            else if (operation == "-") {
                boundValue -= expressionBoundValue;
            }
            else if (operation == "*") {
                boundValue *= expressionBoundValue;
            } 
        }
        operation = expression->operation->name;
    }

    return boundValue;
}

void QF_LIA_logic::getAssertionStatements(std::ostringstream &output) {
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
            string expression = "or";
            for (auto singleElement: statement->leftElements){
                if (dynamic_cast<ExpressionTerm*>(singleElement->terms.front())) {
                    auto domainExpression = dynamic_cast<ExpressionTerm*>(singleElement->terms.front());
                    int boundValue = 0;
                    int lowerBound = 0;
                    bool lowerBoundFlag = false;
                    int upperBound = 0;
                    for (auto child: domainExpression->children) {
                        if (dynamic_cast<NumericTerm*>(child)) {
                            NumericTerm* num = dynamic_cast<NumericTerm*>(child);
                            boundValue = num->value;
                        }
                        else if (dynamic_cast<ExpressionTerm*>(child)) {
                            ExpressionTerm* exp = dynamic_cast<ExpressionTerm*>(child);
                            boundValue = getValue(exp);
                        }
                        
                        // Assign first value to lower bound and second value to upper bound
                        if (!lowerBoundFlag) {
                            lowerBound = boundValue;
                            lowerBoundFlag = true;
                        }
                        else {
                            upperBound = boundValue;
                        }
                    }

                    expression += " " + SMT::Expr("<=", {
                        to_string(lowerBound),
                        SMT::ToString(statement->rightTerm),
                        to_string(upperBound)
                    });

                }

                // if (dynamic_cast<ExpressionTerm*>(singleElement->terms.front())) {
                //     auto domainExpression = dynamic_cast<ExpressionTerm*>(singleElement->terms.front());
                //     NumericTerm* lowerBound = dynamic_cast<NumericTerm*>(domainExpression->children.front());
                //     NumericTerm* upperBound = dynamic_cast<NumericTerm*>(domainExpression->children.back());
                //     expression += " " + SMT::Expr("<=", {
                //         SMT::ToString(lowerBound),
                //         SMT::ToString(statement->rightTerm),
                //         SMT::ToString(upperBound)
                //     });
                // }
                else if (dynamic_cast<NumericTerm*>(singleElement->terms.front())) {
                    auto numericTerm = dynamic_cast<NumericTerm*>(singleElement->terms.front());
                    expression += " " + SMT::Expr("=", {
                        SMT::ToString(statement->rightTerm),
                        SMT::ToString(numericTerm)
                    });
                }
            }
            expression = "(" + expression + ")";
            output << SMT::Assert(expression);
        }
        else {
            LOG(FATAL) << "The " << statement->symbolicTerm->name << " statement is not supported with the logic.";
        }
    }
}

list<SymbolicTerm*> QF_LIA_logic::getConstraintVariables() {
    list<SymbolicTerm*> variables;
    for (auto pair : symbolicTerms) {
        variables.push_back(pair.second);
    }
    return variables;
}

string QF_LIA_logic::toString(TheoryAtomElement* element) {
    if (element->literals.empty()) {
        list<string> terms;
        for (auto term : element->terms) {
            terms.push_back(SMT::ToString(term));
        }

        return SMT::Expr("+", terms, true);
    }

    LOG(FATAL) << "Not yet supported";
}
