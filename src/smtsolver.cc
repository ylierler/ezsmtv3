#include "smtsolver.h"
#include <cstring>
#include <fstream>
#include <ostream>
#include <sstream>
#include <iostream>
#include <regex>
#include <iostream>
#include <unistd.h>
#include <glog/logging.h>

// class ProcessCommunicator
// {
// public:
//     void ExecuteProcess(string executablePath)
//     {
//         int pipeP2C[2], pipeC2P[2];
//         // (names: short for pipe for X (writing) to Y with P == parent, C == child)

//         if(pipe(pipeP2C) != 0 || pipe(pipeC2P) != 0)
//         {
//             // error
//             // TODO: appropriate handling
//         }
//         else
//         {
//             int pid = fork();
//             if(pid < 0)
//             {
//                 // error
//                 // TODO: appropriate handling
//             }
//             else if(pid > 0)
//             {
//                 cout << "Parent started" << endl;
//                 // parent
//                 // close unused ends:
//                 close(pipeP2C[0]); // read end
//                 close(pipeC2P[1]); // write end

//                 // use pipes to communicate with child...
//                 cout << "made it to here" << endl;
//                 cout << pipeC2P[0]

//                 int status;
//                 waitpid(pid, &status, 0);

//                 // cleanup or do whatever you want to do afterwards...
//             }
//             else
//             {
//                 cout << "Child started" << endl;
//                 // child
//                 close(pipeP2C[1]); // write end
//                 close(pipeC2P[0]); // read end
//                 dup2(pipeP2C[0], STDIN_FILENO);
//                 dup2(pipeC2P[1], STDOUT_FILENO);
//                 // you should be able now to close the two remaining
//                 // pipe file desciptors as well as you dup'ed them already
//                 // (confirmed that it is working)
//                 close(pipeP2C[0]);
//                 close(pipeC2P[1]);

//                 char * environment[0];
//                 char * const p = new char[executablePath.length()];
//                 strcpy(p,executablePath.c_str());
//                 char * const command[] = {p};

//                 execve(executablePath.c_str(), command, environment); // won't return - but you should now be able to
//                                 // use stdin/stdout to communicate with parent
//             }
//         }
//     }
// };

// call EZSMT and SMT solver
void SMTSolver::callSMTSolver(SMTSolverCommand solver, Program &program) {
    string solverCommand = "";
    if (solver == CVC4)
        solverCommand = "$EZSMTPLUS/tools/cvc4 --lang smt --output-lang smtlib2.6 ";
    else if (solver == Z3)
        solverCommand = "$EZSMTPLUS/tools/z3 -smt2 ";
    else if (solver == YICES)
        solverCommand = "$EZSMTPLUS/tools/yices-smt2 ";

    stringstream ss;

    string smtFileName = "output.smt";

    string programBody = getProgramBodyString(program);
    string programCheckSatFooter = getCheckSatString(program);

    int i = 1;
    while (true) {
        string completeProgram = programBody + programCheckSatFooter;
        writeToFile(completeProgram, smtFileName);

        system((solverCommand + " " + smtFileName + " > temp.smtlib").c_str());

        vector<string> resultAnswerSets;
        bool isSatisfiable = parseSolverResults("temp.smtlib", resultAnswerSets);

        if (!isSatisfiable)
        {
            break;
        }

        cout << "Answer set " << i << ": ";
        for (auto smtAtom: resultAnswerSets)
        {
            cout << smtAtom << " ";
        }
        cout << endl;

        programBody += getAnswerSetNegationString(resultAnswerSets);

        i++;
    }
}

void SMTSolver::writeToFile(string input, string outputFileName)
{
    ofstream outputStream;
    outputStream.open(outputFileName);
    outputStream << input;
    outputStream.close();

    VLOG(2) << "Wrote SMT-LIB file:" << endl << input << endl;
}

bool SMTSolver::parseSolverResults(string resultsFileName, vector<string>& resultAnswerSet)
{
    resultAnswerSet.clear();
    ifstream inputStream(resultsFileName);

    string satResult;
    std::getline(inputStream, satResult);

    if (satResult == "unsat")
    {
        return false;
    }

    stringstream atomsListStream;
    string line;
    while(std::getline(inputStream, line)) {
        atomsListStream << line;
    }
    string atomsList = atomsListStream.str();

    regex r ("\\((\\|[^ ]*\\|) true\\)");
    smatch match;
    string::const_iterator searchStart(atomsList.cbegin());
    while (regex_search(searchStart, atomsList.cend(), match, r))
    {
        searchStart = match.suffix().first;
        resultAnswerSet.push_back(match[1].str());
    }

    return true;
}

string SMTSolver::getAnswerSetNegationString(vector<string>& answerSet)
{
    // TODO Should I include negatives (false)?

    ostringstream output;
    output << "(assert (not (and";
    for (string smtAtom : answerSet)
    {
        output << " " << smtAtom;
    }
    output << ")))" << endl;

    VLOG(2) << "Generated answer set negation:" << endl << output.str();
    return output.str();
}

string SMTSolver::getCheckSatString(Program& program)
{
    ostringstream output;
    output << "(check-sat)" << endl;

    output << "(get-value (";
    for (Atom* a : program.atoms)
    {
        if (a->name)
        {
            output << a->getSmtName() << " ";
        }
    }
    output << "))" << endl;

    return output.str();
}

// FIXME this is copying strings
string SMTSolver::getProgramBodyString(Program& program)
{
    // ofstream outputFileStream;
    // outputFileStream.open(outputFileName);
    ostringstream output;

    output << "(set-info :smt-lib-version 2.6)" << endl;
    output << "(set-option :produce-models true)" << endl;
    output << "(set-option :produce-assignments true)" << endl;
    output << "(set-logic ALL)" << endl;

    for (Atom* a : program.atoms)
    {
        // FIXME Should this declare a const or fun?
        output << "(declare-fun " << a->getSmtName() << " () Bool)" << endl;
    }

    for (Clause* c : program.clauses)
    {
        output << "(assert " << c->toSmtLibString() << ")" << endl;
    }

    return output.str();

    // TODO output computeTrue atoms
    // output <<
    // for (Atom* a : program.atoms)
    // {
    // 	if (a->computeTrue)
    // 	{
    // 		output << "(assert " << c->toSmtLibString() << ")" << endl;
    // 	}
    // }


    // output.close();

    // system(string("cat " + outputFileName).c_str());
}
