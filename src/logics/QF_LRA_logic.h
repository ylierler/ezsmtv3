#ifndef QF_LRA_logic_H_
#define QF_LRA_logic_H_


#include <sstream>
#include "program.h"
// #include "logic.h"
#include "QF_LIA_logic.h"

class QF_LRA_logic : public QF_LIA_logic {
public:
    string SMT_LOGIC_NAME() override;
    void getDeclarationStatements(std::ostringstream &output) override;
};

#endif // QF_LRA_logic_H_