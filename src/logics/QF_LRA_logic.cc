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
