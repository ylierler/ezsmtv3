#include "smtlogics.h"
#include "glog/logging.h"

string QF_LIA::SMT_LOGIC_NAME() { return "QF_LIA"; }

void QF_LIA::processTheoryStatement(TheoryStatement *statement) {
    if (statement->symbolicTerm == "sum") {
        for (auto element : statement->leftElements) {
            for (auto term : element->terms) {
                if (term->type == SYMBOLIC) {
                    symbolicTerms[term->id] = term;
                }
            }
        }
    } else {
        LOG(FATAL) << "The EZSMTPLUS " << SMT_LOGIC_NAME() << " implementation does not support symbolic term " << statement->symbolicTerm;
    }
}

void QF_LIA::getDeclarationStatements(std::ostringstream &output) {
    for (const auto p : symbolicTerms) {
        auto term = p.second;
        output << "(declare-const " << term->value << " Int)" << endl;
    }
}

void QF_LIA::getAssertionStatements(std::ostringstream &output) {

}
