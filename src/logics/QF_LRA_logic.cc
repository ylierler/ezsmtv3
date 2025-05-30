#include "logic.h"
#include "QF_LRA_logic.h"
#include "glog/logging.h"
#include "program.h"
#include <numeric>
#include "smtstringhelpers.h"


/*if both types ints and reals are present, return LIRA logic
levelRanking flag is set to true in case of non-tight LRA program, where level ranking variables are integers
typeMap is the map with custom specified types for LIRA logic*/
string QF_LRA_logic::SMT_LOGIC_NAME() {
    if (levelRanking || optimization || typeMap.size()) {
        return "AUFLIRA";
    }
    return "QF_LRA";
}

void QF_LRA_logic::getDeclarationStatements(std::ostringstream &output) {
    for (const auto p : this->symbolicTerms) {
        auto term = p.second;
        string termName = term->name;

        if (typeMap.size()) {
            int index = termName.find("(");
            string functionalName = termName.substr(0, index);

            string type = "";
            if (typeMap.find(termName) != typeMap.end()) {
                type = typeMap[termName];
            }
            else if (typeMap.find(functionalName) != typeMap.end()) {
                type = typeMap[functionalName];
            }
            
            if (type == "int") {
                output << SMT::DeclareConst(termName, "Int");
                continue;
            }
        }
        output << SMT::DeclareConst(termName, "Real");
    }
}

string QF_LRA_logic::getIndividualRealTermAssertionStatement(ITheoryTerm* rightTerm, RealTerm* realTerm) {
    string valueString = getString(realTerm->value);
    return getIndividualValueAssertionStatement(rightTerm, valueString);
}

float QF_LRA_logic::getRealTermValue(RealTerm* num) {
    return num->value;
}

string QF_LRA_logic::getString(float value) {
    return to_string(value);
}