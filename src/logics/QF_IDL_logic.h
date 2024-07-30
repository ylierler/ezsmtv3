#ifndef QF_IDL_logic_H_
#define QF_IDL_logic_H_

#include "QF_LIA_logic.h"

class QF_IDL_logic : public QF_LIA_logic {
public:
    string SMT_LOGIC_NAME() override;
    void getAssertionStatements(std::ostringstream &output) override;
};

#endif // QF_IDL_logic_H_