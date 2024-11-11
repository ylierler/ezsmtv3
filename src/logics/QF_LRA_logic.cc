#include "logic.h"
#include "QF_LRA_logic.h"
#include "glog/logging.h"
#include "program.h"
#include <numeric>
#include "smtstringhelpers.h"


/*if both types ints and reals are present, return IRA logic
mixed is true in case of non-tight program, where level ranking variables are integers
typeMap is the map with custom specified types for IRA logic*/
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
