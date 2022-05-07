#ifndef SMTSOLVER_H_
#define SMTSOLVER_H_

#include "program.h"
#include "param.h"
#include <boost/process.hpp>

class SMTSolver
{
    public:

        void callSMTSolver(Param &params, Program &program);

    private:
        bool parseSolverResults(boost::process::ipstream& inputStream, vector<string>& resultAnswerSet);
        string getProgramBodyString(Program& program);
        string getCheckSatString(Program& program);
        string getAnswerSetNegationString(vector<string>& answerSet);
        void writeToFile(string input, string outputFileName);
};


#endif // SMTSOLVER_H_
