#include "logic.h"
#include "QF_LIA_logic.h"
#include "glog/logging.h"
#include "program.h"
#include <numeric>
#include "smtstringhelpers.h"

string QF_LIA_logic::SMT_LOGIC_NAME() { return "QF_LIA"; }

void QF_LIA_logic::processTheoryStatements(list<TheoryStatement*> statements) {
    this->statements = statements;

    // lambda helper function for recursion on nested expression terms
    std::function<void(ExpressionTerm*)> helper = [&](ExpressionTerm* expressionTerm) {
        for (auto exp: expressionTerm->children) {
            if (auto s = dynamic_cast<SymbolicTerm*>(exp)) {
                this->symbolicTerms[s->id] = s;
            }
            else if (auto s = dynamic_cast<ExpressionTerm*>(exp)) {
                helper(s);
            }
        }
    };

    for (auto statement : statements) {
        statement->traverseNestedTerms([&](ITheoryTerm* term) {
            if (auto s = dynamic_cast<SymbolicTerm*>(term)) {
                this->symbolicTerms[s->id] = s;
            }
            else if (auto s = dynamic_cast<ExpressionTerm*>(term)) {
                helper(s);
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

int QF_LIA_logic::solveExpression(ExpressionTerm* expression) {
    string operation="+";
    int value = 0;

    for (auto child: expression->children) {
        int termValue = 0;

        if (auto num = dynamic_cast<NumericTerm*>(child)) {
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

int QF_LIA_logic::getTermValue(ITheoryTerm* term) {
    if (auto num = dynamic_cast<NumericTerm*>(term)) {
        return num->value;
    }
    else if (auto exp = dynamic_cast<ExpressionTerm*>(term)) {
        return solveExpression(exp);
    }
    LOG(FATAL) << "Invalid syntax for dom statement." << endl;
}

tuple<int, int> QF_LIA_logic::getLowerAndUpperBounds(ExpressionTerm* domainExpression) {
    ITheoryTerm* lbTerm = domainExpression->children.front();
    ITheoryTerm* ubTerm = domainExpression->children.back();
        
    int lowerBound = getTermValue(lbTerm);
    int upperBound = getTermValue(ubTerm);
    return make_tuple(lowerBound, upperBound);
}

string QF_LIA_logic::getSumAssertionStatement(TheoryStatement* statement) {
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
    return assertion;
}

string QF_LIA_logic::getUnaryOrLowerUpperBoundAssertionStatements(ExpressionTerm* domainExpression, ITheoryTerm* rightTerm) {
    // check for unary values 
    if (
        domainExpression->children.size() == 1
        && dynamic_cast<NumericTerm*>(domainExpression->children.front()) 
    ){
        NumericTerm* num = dynamic_cast<NumericTerm*>(domainExpression->children.front());
        int value = num->value;

        string unaryAssertionStatement = to_string(value);
        if (domainExpression->operation->name == "-") {
            unaryAssertionStatement = "(- " + unaryAssertionStatement + ")";
        }

        string expression = " " + SMT::Expr("=", {
            SMT::ToString(rightTerm),
            unaryAssertionStatement
        });

        return expression;
    }

    // for .. operation with lower-bound and upper-bound
    else {
        auto boundTuple = getLowerAndUpperBounds(domainExpression);
        int lowerBound = get<0>(boundTuple);
        int upperBound = get<1>(boundTuple);

        string expression = " " + SMT::Expr("<=", {
            to_string(lowerBound),
            SMT::ToString(rightTerm),
            to_string(upperBound)
        });

        return expression;
    }
}

void QF_LIA_logic::getAssertionStatements(std::ostringstream &output) {
    for (const auto statement : statements) {
        string assertion;

        if (statement->symbolicTerm->name == "sum")  {
            assertion = getSumAssertionStatement(statement);
        }
        
        else if (statement->symbolicTerm->name == "dom") {
            string expression = "or";
            for (auto singleElement: statement->leftElements){
                // for expression term with unary values, and lower-bound and upper-bound inside dom
                if (auto domainExpression = dynamic_cast<ExpressionTerm*>(singleElement->terms.front())) {
                    expression += getUnaryOrLowerUpperBoundAssertionStatements(domainExpression, statement->rightTerm);
                }

                // for individual values inside dom
                else if (auto numericTerm = dynamic_cast<NumericTerm*>(singleElement->terms.front())) {
                    expression += " " + SMT::Expr("=", {
                        SMT::ToString(statement->rightTerm),
                        SMT::ToString(numericTerm)
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
