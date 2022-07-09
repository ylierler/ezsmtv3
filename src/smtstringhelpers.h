#ifndef SMTSTRINGHELPERS_H_
#define SMTSTRINGHELPERS_H_

#include <list>
#include <regex>
#include <sstream>
#include <string>
#include "theory.h"

using namespace std;

class SMT {
public:
    static string Var(string name) {
        if (regex_match(name, regex(".*[(),0-9]+.*"))) {
            return "|" + name + "|";
        } else {
            return name;
        }
    }

    static string Expr(string operation, const list<string>& arguments, bool passThoughIfSingleArg = false) {
        if (passThoughIfSingleArg && arguments.size() == 1) {
            return arguments.front();
        }

        ostringstream output;
        output << "(" << operation;
        for (auto arg : arguments) {
            output << " " << arg;
        }
        output << ")";
        return output.str();
    }

    static string Assert(string expression) {
        ostringstream output;
        output << "(assert " << expression << ")" << endl;
        return output.str();
    }

    static string ToString(Atom* atom) {
        return Var(atom->name != nullptr ? atom->name : to_string(atom->id));
    }

    static string TheoryTerm(ITheoryTerm* term) {
        if (auto t = dynamic_cast<NumericTerm*>(term)) {
            return to_string(t->value);
        } else if (auto t = dynamic_cast<SymbolicTerm*>(term)) {
            return Var(t->name);
        } else if (auto t = dynamic_cast<TupleTerm*>(term)) {
            if (t->type == PARENTHESES) {
                return string("(") + TheoryTerm(*(t->children.begin())) + ")";
            }
        } else if (auto t = dynamic_cast<ExpressionTerm*>(term)) {
            list<string> childTerms;
            for (auto term : t->children) {
                childTerms.push_back(TheoryTerm(term));
            }
            return SMT::Expr(t->operation->name, childTerms);
        }

        LOG(FATAL) << "Unsupported term type";
    }
};


#endif // SMTSTRINGHELPERS_H_
