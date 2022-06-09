#include "smtlogics.h"
#include "glog/logging.h"
#include "program.h"
#include <numeric>

string QF_LIA::SMT_LOGIC_NAME() { return "QF_LIA"; }

void QF_LIA::processTheoryStatements(list<TheoryStatement*> statements) {
    for (auto statement : statements) {
        if (statement->symbolicTerm->name == "sum") {
            this->statements.push_back(statement);
            for (auto element : statement->leftElements) {
                for (auto term : element->terms) {
                    if (SymbolicTerm* s = dynamic_cast<SymbolicTerm*>(term)) {
                        symbolicTerms[s->id] = s;
                    }
                }
            }
            if (SymbolicTerm* s = dynamic_cast<SymbolicTerm*>(statement->rightTerm)) {
                symbolicTerms[s->id] = s;
            }
        } else {
            LOG(FATAL) << "The " << SMT_LOGIC_NAME() << " logic implementation does not support " << statement->symbolicTerm;
        }
    }
}

void QF_LIA::getDeclarationStatements(std::ostringstream &output) {
    for (const auto p : symbolicTerms) {
        auto term = p.second;
        output << "(declare-const " << term->name << " Int)" << endl;
    }
}

void QF_LIA::getAssertionStatements(std::ostringstream &output) {
    for (const auto statement : statements) {
        if (statement->symbolicTerm->name != "sum")  {
            LOG(FATAL) << "The EZSMTPLUS " << SMT_LOGIC_NAME() << " implementation does not support symbolic term " << statement->symbolicTerm;
        }

        output << "(assert (" << statement->operation->name;

        for (const auto element : statement->leftElements) {
            output << " " << toString(element);
        }

        output << " " << toString(statement->rightTerm) << "))" << endl;
    }
}

string QF_LIA::toString(TheoryAtomElement* element) {
    if (element->literals.empty()) {
        if (element->terms.size() == 1) {
            return toString(*(element->terms.begin()));
        }
        string output = "(+";
        for (const auto term : element->terms) {
            output += " " + toString(term);
        }
        output += ")";
        return output;
    }

    LOG(FATAL) << "Not yet supported";
}

string QF_LIA::toString(ITheoryTerm* term) {
    if (auto t = dynamic_cast<NumericTerm*>(term)) {
        return to_string(t->value);
    } else if (auto t = dynamic_cast<SymbolicTerm*>(term)) {
        return t->name;
    } else if (auto t = dynamic_cast<TupleTerm*>(term)) {
        if (t->type == PARENTHESES) {
            return string("(") + toString(*(t->children.begin())) + ")";
        }
    } else if (auto t = dynamic_cast<CompoundTerm*>(term)) {
        string childTerms = std::reduce(t->children.begin(), t->children.end(), string(),
            [&](string current, ITheoryTerm* next) {
                return current + " " + toString(next);
            });
        return "(" + t->operation->name + childTerms + ")";
    }

    LOG(FATAL) << "Unsupported term type";
}
