#ifndef SMTSOLVER_H_
#define SMTSOLVER_H_

#include "program.h"
class SMTSolver
{
    public:

        void callSMTSolver(SMTSolverCommand solver, Program &program);

    private:
        bool parseSolverResults(string resultsFileName, vector<string>& resultAnswerSet);
        void writeToSmtLibFile(Program &program, string outputFileName);
};


#endif // SMTSOLVER_H_
