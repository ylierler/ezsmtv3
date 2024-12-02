#ifndef QF_LRA_logic_H_
#define QF_LRA_logic_H_

#include "QF_LIA_logic.h"

class QF_LRA_logic : public QF_LIA_logic {
public:
    bool mixed_logic;
    map<string, string> typeMap;
    QF_LRA_logic(bool mixed_logic, map<string, string> typeMap) : mixed_logic(mixed_logic), typeMap(typeMap) {};
    string SMT_LOGIC_NAME() override;
    void getDeclarationStatements(std::ostringstream &output) override;

    string getIndividualRealTermAssertionStatement(ITheoryTerm* rightTerm, RealTerm* realTerm) override;
    float getRealTermValue(RealTerm* num) override;
    string getString(float value) override;
};

#endif // QF_LRA_logic_H_