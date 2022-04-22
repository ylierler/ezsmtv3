#include "smtsolver.h"
#include <fstream>
#include <sstream>
#include <iostream>
#include <regex>


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
    writeToSmtLibFile(program, smtFileName);

    cout << solverCommand << endl;

    vector<string> resultAnswerSets;
    int i = 1;
    do {
        system((solverCommand + " " + smtFileName + " > temp.smtlib").c_str());
        system("cat temp.smtlib");
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

        i++;
    } while (i == 1);
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

void SMTSolver::writeToSmtLibFile(Program& program, string outputFileName)
{
    ofstream outputFileStream;
    outputFileStream.open(outputFileName);

    outputFileStream << "(set-info :smt-lib-version 2.6)" << endl;
    outputFileStream << "(set-option :produce-models true)" << endl;
    outputFileStream << "(set-option :produce-assignments true)" << endl;
    outputFileStream << "(set-logic ALL)" << endl;

    for (Atom* a : program.atoms)
    {
        // FIXME Should this declare a const or fun?
        outputFileStream << "(declare-fun " << a->getSmtName() << " () Bool)" << endl;
    }

    for (Clause* c : program.clauses)
    {
        outputFileStream << "(assert " << c->toSmtLibString() << ")" << endl;
    }

    // TODO output computeTrue atoms
    // outputFileStream <<
    // for (Atom* a : program.atoms)
    // {
    // 	if (a->computeTrue)
    // 	{
    // 		outputFileStream << "(assert " << c->toSmtLibString() << ")" << endl;
    // 	}
    // }

    outputFileStream << "(check-sat)" << endl;

    outputFileStream << "(get-value (";
    for (Atom* a : program.atoms)
    {
        if (a->name)
        {
            outputFileStream << a->getSmtName() << " ";
        }
    }
    outputFileStream << "))" << endl;

    outputFileStream.close();

    system(string("cat " + outputFileName).c_str());

    // FIXME Carry over from print_DIMACS
    //clean memory from clauses that will no longer be of use
    // if (param.sys == CASP_DIMACS_PRODUCE || param.sys == DIMACS_PRODUCE
    //         || param.sys == SCC_LEVEL_RANKING || param.sys == LEVEL_RANKING
    //         || param.sys == SCC_LEVEL_RANKING_STRONG
    //         || param.sys == LEVEL_RANKING_STRONG
    //         || (program.tight
    //                 && (param.sys == RELSAT || param.sys == ASSAT_ZCHAFF))
    //         || param.sys == SIMO) {
    //     for (long indA = 0; indA < program.clauses.size(); indA++) {
    //         delete program.clauses[indA];
    //     }
    //     program.clauses.clear();
    // }
}
