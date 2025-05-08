#ifndef QF_LRA_logic_H_
#define QF_LRA_logic_H_

#include "QF_LIA_logic.h"

class QF_LRA_logic : public QF_LIA_logic {
public:
    bool levelRanking;
    bool optimization;
    map<string, string> typeMap;
    QF_LRA_logic(bool levelRanking, bool minization, map<string, string> typeMap) : 
                    levelRanking(levelRanking), optimization(optimization), typeMap(typeMap) {};
    string SMT_LOGIC_NAME() override;
    void getDeclarationStatements(std::ostringstream &output) override;

    string getIndividualRealTermAssertionStatement(ITheoryTerm* rightTerm, RealTerm* realTerm) override;
    float getRealTermValue(RealTerm* num) override;
    string getString(float value) override;
};

#endif // QF_LRA_logic_H_