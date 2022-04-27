#ifndef SMTSOLVER_H_
#define SMTSOLVER_H_

#include "program.h"
class SMTSolver
{
    public:

        void callSMTSolver(SMTSolverCommand solver, Program &program);

    private:
        bool parseSolverResults(string resultsFileName, vector<string>& resultAnswerSet);
        string getProgramBodyString(Program& program);
        string getCheckSatString(Program& program);
        string getAnswerSetNegationString(vector<string>& answerSet);
        void writeToFile(string input, string outputFileName);
};


#endif // SMTSOLVER_H_
