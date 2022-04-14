#include <iostream>
#include <regex>
#include <string.h>
#include <string>
#include <sys/types.h>
#include <sys/time.h>
#include <unistd.h>
#include <limits.h>
#include <float.h>
#include <stdlib.h>
#include <assert.h>
#include <stdio.h>
#include <fstream>
#include <cstdlib>
#include <cstdio>

#include <set>
#include <vector>
#include <list>
#include <algorithm>

#include "print.h"
#include "interpret.h"
#include "atomrule.h"
#include "cmodels.h"
#include "defines.h"
#include "SAT.h"
#include <sstream>
#include <ctype.h>

using namespace std;

#define MAX_LINE_LENGTH    65536
#define MAX_WORD_LENGTH    64


/* if you want some statistics during the solving, uncomment following line */
//    SAT_AddHookFun(mng,output_status, 5000);
Cmodels::Cmodels() {
	output.program = &program;
	output.param = &param;

	satMngMinimality = 0;
	zchaffMng = 0;
	LRVarIDs.clear();

}

void Cmodels::initRuleLists4WF() {

	for (list<Rule*>::iterator ir = program.rules.begin();
			ir != program.rules.end(); ir++) {
		//	(*ir)->print();
		(*ir)->initRuleLists4WF();
	}
}
void Cmodels::findSameBodies() {
	vector<NestedRule*> rules;
	for (vector<Atom*>::iterator ia = program.atoms.begin();
			ia != program.atoms.end(); ia++)
		for (list<NestedRule*>::iterator ir = (*ia)->nestedRules.begin();
				ir != (*ia)->nestedRules.end(); ir++)
			rules.push_back((*ir));

	api->sortBodyRuleList(rules, (long) rules.size());
	NestedRule* cur;
	NestedRule* next;
	int num = 0;
	for (vector<NestedRule*>::iterator ir = rules.begin(); ir != rules.end();) {
		cur = (*ir);
		ir++;
		if (ir == rules.end())
			break;
		else
			next = (*ir);

		if (cur->end - cur->nbody > 1) {

			if (cur->cmpBody(next) == EQ) {	//if bodies coincide
				//		cur->print();
				//		next->print();
				num++;
				if (cur->reprComp == 0) {

					createRepresentative(cur);
				}
				next->reprComp = cur->reprComp;
				next->signReprComp = cur->signReprComp;
			}
		}
	}
	output.numSameBodies = num;
	rules.clear();

}
void Cmodels::sortRules() {
	//we init the head rules lists
	for (list<Rule*>::iterator ir = program.rules.begin();
			ir != program.rules.end(); ir++) {
		(*ir)->initHeadRuleLists4Sort();
	}

	for (vector<Atom*>::iterator ia = program.atoms.begin();
			ia != program.atoms.end(); ia++) {
		//	(*ia)->print();
		//cout<<" "<<(long)(*ia)->headRules.size()<<endl;
		api->sortRuleList((*ia)->headRules, (long) (*ia)->headRules.size());
		/*
		 for(vector<Rule*>::iterator irr=(*ia)->headRules.begin();
		 irr!=(*ia)->headRules.end();irr++){

		 if((*irr)->erase){
		 cout<<" ERASE ";
		 (*irr)->print();
		 }
		 else
		 (*irr)->print();

		 }
		 */
	}
	list<Rule*>::iterator ir = program.rules.begin();
	program.number_of_rules = 0;
	while (ir != program.rules.end()) {
		if ((*ir)->erase) {
			delete (*ir);
			ir = program.rules.erase(ir);
		} else {
			program.number_of_rules++;
			ir++;
		}
	}
	//clear atoms headlists since they will be used later
	for (vector<Atom*>::iterator ir = program.atoms.begin();
			ir != program.atoms.end(); ir++) {
		(*ir)->headRules.clear();

	}
}

//
//well founded model computation
//translation into nested normal from (elimination of weigth constraints
//

Result Cmodels::preprocessing(bool& emptyprogram) {
	emptyprogram = false;

	if (program.number_of_atoms > 0) {
		if (strcmp(program.atoms.front()->atom_name(), "#noname#") == 0
				&& program.atoms.front()->Bneg) {
			program.false_atom = program.atoms.front();
		}
	}
	//at this point we have read in all the rules
	//now i would  like to go through the list of rules and sort it

	//  vector<Rule*> tempRules; //for sorting
	/*    cout<<"Number of Rules "<<program.number_of_rules<<endl;
	 cout<<"First Program "<<endl;
	 program.print();
	 */
	output.numRules = program.number_of_rules;
	sortRules();


	initRuleLists4WF();
	cout<<"Final Program "<<endl;
	program.print();
	cout << endl;

	// exit(0);
	bool conflict = false;
	conflict = wellFounded();
	if (param.sys != SCC_LEVEL_RANKING && param.sys != LEVEL_RANKING
			&& param.sys != SCC_LEVEL_RANKING_STRONG
			&& param.sys != LEVEL_RANKING_STRONG)
		param.sys = SCC_LEVEL_RANKING;
	if (param.sys != DIMACS_PRODUCE && param.sys != CASP_DIMACS_PRODUCE
			&& param.sys != SCC_LEVEL_RANKING && param.sys != LEVEL_RANKING
			&& param.sys != SCC_LEVEL_RANKING_STRONG
			&& param.sys != LEVEL_RANKING_STRONG) {
		if (param.cm_wfm) {
			printWFM();
			exit(0);
		}

		if (conflict) {
			return UNSAT;
		}

		if (completeWFM()) {  //if WFM is comlete then it is AS
			return SAT;
		}

		//  exit(0);
		if (pt()) {  // DLV pt operator if true then WFM is AS
			//if either weight or constraint or choice rule appears
			//pt operator will return false
			//otherwise it computes pt
			return SAT;
		}
	}
	//  program.print();
	output.timerTranslation.start();
	if (translate_all_to_nested_rules()) {
		param.verifyMethod = NONDISJ;
		program.disj = false;
	}
	if (param.sort)
		findSameBodies();

	//Report an error if the program is disjunctive.
	if (program.disj) {
		// FIXME What does disjunctive mean?
		cerr << "Error: disjunctive programs are not supported." << endl;
		exit(-1);
	}

	output.timerTranslation.stop();
	//tightness verification
	//hcf verification
	long numSCC = 0;
	markProgramsSCC(numSCC, true);
	if (numSCC == 0) {
		program.tight = true;
	} else {
		program.tight = false;
		if (param.printCycle)
			printCycles(numSCC);
	}
	output.tight_output();
	if (program.tight)
		param.verifyMethod = TIGHT;
	output.disj_output();

	//output.timerCompletion.start();
	//createCompletion();
	//output.timerCompletion.stop();

	//  cout<<"Completion..."<<endl;

	if (program.tight) {
		output.timerCompletion.start();
		createCompletion();
		output.timerCompletion.stop();
	} else {
		output.timerCompletion.start();
		createCompletion();
		output.timerCompletion.stop();
	}

	//if we want to add SCC level ranking formula
	if (param.sys == SCC_LEVEL_RANKING
			or param.sys == SCC_LEVEL_RANKING_STRONG) {
		if (program.tight)
			cout << "Program is tight, no level ranking formula is added."
					<< endl;
		else {
			output.timerCompletion.start();
			createSCCRankingFormula();
			output.timerCompletion.stop();
		}

	}

	//if we want to add level ranking formula
	if (param.sys == LEVEL_RANKING or param.sys == LEVEL_RANKING_STRONG) {
		if (program.tight)
			cout << "Program is tight, no level ranking formula is added."
					<< endl;
		else {
			output.timerCompletion.start();
			createRankingFormula();
			output.timerCompletion.stop();
		}

	}

	//if program is disjunctive and nontight we verify if it is HCF
	if (!program.tight && program.disj) {
		if (HCFverification(numSCC)) {
			param.verifyMethod = HCF;
			program.hcf = true;
		}
		output.hcf_output();

	}
	//at this point we can initiate pbodies
	//as all the false atoms (contsraints false:-body) rules are out of
	//the program and therefore only relevant rules would be added to list
	if (!program.tight) {
		initPBodyRules();
		clearInLoop(); //clear inLoop atoms for future computation
		//as we already used this function
	}

	//    cout<<"Clausification..."<<endl;

	output.timerClausification.start();

	if (createClauses() == UNSAT) {
		return UNSAT;
	}

	eraseFalseAtomsFromClauses();
	createSingleAtomClauses();	//from Bpos and Bneg
	output.timerClausification.stop();

	if (program.number_of_clauses <= 0) { //initial or after wf the program  is empty
		emptyprogram = true;
		return SAT;
	}


	setupFilenames();

	return (Result) UNKNOWN;
}

void Cmodels::init(int* answerset_lits, int& num_atoms,
		const char **&symbolTable, int &symbolTableEntries) {
	num_atoms = -2;
	Result ret = (Result) UNKNOWN;
	bool programempty = false;
	ret = preprocessing(programempty);
	switch (ret) {
	case SAT: {
		if (!programempty)
			populate_answerset_lits_wfm(answerset_lits, num_atoms);
		else
			num_atoms = 0;
		break;
	}
	case UNSAT: {
		num_atoms = -1;
		break;

	}
	}

	int maxid = 0;
	for (int i = 0; i < program.number_of_atoms; i++)
		if (program.atoms[i]->get_lparse_id() > maxid)
			maxid = program.atoms[i]->get_lparse_id();
	symbolTableEntries = maxid;
	symbolTable = (const char **) calloc(symbolTableEntries + 1,
			sizeof(const char *));
	for (int i = 0; i < program.number_of_atoms; i++)
		if (program.atoms[i]->get_lparse_id() >= 0) {
			const char *s = program.atoms[i]->atom_name();
			symbolTable[program.atoms[i]->get_lparse_id()] = s;
		}
}

void Cmodels::populate_answerset_lits_wfm(int* answerset_lits, int& num_atoms) {
	num_atoms = 0;
	for (long i = 0; i < program.number_of_atoms; i++) {
		if (program.atoms[i]->Bpos && program.atoms[i]->get_lparse_id() != -1) {
			answerset_lits[num_atoms] = program.atoms[i]->get_lparse_id();
			num_atoms++;
		}
	}

}

string convertCNFTermToSmtTerm(string term)
{
	if (term.find("-") == std::string::npos)
	{
		return term;
	}
	else
	{
		return term.replace(term.find("-"), 1, "(not ") + ")";
	}
}

string convertCNFLineToSMTAssertion(string line)
{
	istringstream input(line);
	ostringstream output;

	output << "(assert (or";

	string term;
	input >> term;

	while (term != "0")
	{
		cout << term << endl;
		output << " " + convertCNFTermToSmtTerm(term);

		input >> term;
	}
	output << "))";

	return output.str();
}

// call SMT solver to compute one model
void Cmodels::computeOneSMTModel(string fileName, string solverCommand, int fileCount) {
	stringstream ss;
	ss.clear();
	ss.str("");
	cout << "Computing the " << fileCount + 1 << "th answer set"
			<< endl;
	
	if (fileCount == 0)
		ss << solverCommand << fileName;
				// << " > Model" // TODO
				// << fileName.substr(17, fileName.size() - 21);
	else
		ss << solverCommand << "SMT"
				<< fileName.substr(17, fileName.size() - 21) << "_"
				<< fileCount << " > Model"
				<< fileName.substr(17, fileName.size() - 21) << "_"
				<< fileCount;
	cout << "Running command: " << ss.str().c_str() << endl;
	system(ss.str().c_str());
	if (fileCount == 0)
		cout << "Model" << fileName.substr(17, fileName.size() - 21)
				<< " file is produced" << endl;
	else
		cout << "Model" << fileName.substr(17, fileName.size() - 21)
				<< "_" << fileCount << " file is produced" << endl;

	return;
}

// enumerate extended answer sets
void Cmodels::enumerateExtendedAnswerSets(string fileName, string solverCommand, int fileCount, string SMTStr, istringstream* iss) {
	int extfileCount = 0;
	stringstream ss;
	ss.clear();
	ss.str("");
	string line;

	//Make sure that we find the same answer set
	string str_search = "; Check satisfiability";
	string CurVar = "";
	ss.clear();
	ss.str("");
	while (getline(*iss, line)) {
		//if a variable name is read, store it in curVar.
		if ((param.SMTsolver == CVC4 || param.SMTsolver == Z3)
				&& line.find("(define-fun ") != string::npos) {
			int StartPos = line.find("(define-fun ");
			int EndPos = line.find(" () ");
			CurVar = line.substr(StartPos + 12,
					EndPos - StartPos - 12);

		} else if (param.SMTsolver == YICES
				&& line.find("(= ") != string::npos) {

			int StartPos = line.find("(= ");
			if (line.find(" true)") != string::npos) {
				int EndPos = line.find(" true)");
				CurVar = line.substr(StartPos + 3,
						EndPos - StartPos - 3);
			} else if (line.find(" false)") != string::npos) {
				int EndPos = line.find(" false)");
				CurVar = line.substr(StartPos + 3,
						EndPos - StartPos - 3);
			} else {
				//It's not a regular atom, or "false)" and "true)" is pushed into the next line
				//reset curVar
				CurVar = "cspdomain";
				continue;
			}

		} else if (param.SMTsolver == YICES
				&& line.find("(=") != string::npos) {
			//if a variable's name is too long, it will be on the next line in output
			getline(*iss, line);
			CurVar = line;
			getline(*iss, line);
		}

		//if the variable is not level ranking variable
		if (CurVar.find("required(") == string::npos
				&& CurVar.find("cspvar") == string::npos
				&& CurVar.find("cspdomain") == string::npos) {
			// if the variable is asserted to be false
			if (line.find(" false)") != string::npos) {

				if (CurVar.substr(0, 1) == "|") {
					if (!isdigit(CurVar[1]))
						ss << "(assert  (not " << CurVar
								<< "))\n";
				} else {
					if (!isdigit(CurVar[0]))
						ss << "(assert  (not |" << CurVar
								<< "|))\n";
				}
			}
			// if the variable is asserted to be true
			else if (line.find(" true)") != string::npos) {

				if (CurVar.substr(0, 1) == "|") {
					;
					if (!isdigit(CurVar[1]))
						ss << "(assert " << CurVar << ")\n";
				} else {

					if (!isdigit(CurVar[0])) {
						ss << "(assert " << "|" << CurVar
								<< "|)\n";
					}
				}
			}

		}
	}
	ss << "\n; Check satisfiability";
	string str_replace = ss.str();
	size_t assertionPos = SMTStr.find(str_search);

	SMTStr.replace(assertionPos, string(str_search).length(),
			str_replace);

	ss.clear();
	ss.str("");
	if (fileCount == 0)
		ss << "SMT"
				<< fileName.substr(17, fileName.size() - 21);
	else
		ss << "SMT" << fileName.substr(17, fileName.size() - 21)
				<< "_" << fileCount;
	ss << "-0";
	ofstream out_file(ss.str().c_str());
	cerr << "writing SMT file: " << ss.str().c_str() << endl;
	out_file << SMTStr;

	do {
		//Solving
		if (extfileCount != 0) {
			cout << "Computing the " << extfileCount + 1
					<< "th extended answer set" << endl;
			ss.clear();
			ss.str("");
			if (fileCount == 0)
				ss << solverCommand << "SMT"
						<< fileName.substr(17,
								fileName.size() - 21) << "-"
						<< extfileCount << " > Model"
						<< fileName.substr(17,
								fileName.size() - 21) << "-"
						<< extfileCount;
			else
				ss << solverCommand << "SMT"
						<< fileName.substr(17,
								fileName.size() - 21) << "_"
						<< fileCount << "-" << extfileCount
						<< " > Model"
						<< fileName.substr(17,
								fileName.size() - 21) << "_"
						<< fileCount << "-" << extfileCount;
			cout << "Running command: " << ss.str().c_str()
					<< endl;
			system(ss.str().c_str());
			if (fileCount == 0)
				cout << "Model"
						<< fileName.substr(17,
								fileName.size() - 21) << "-"
						<< extfileCount << " file is produced"
						<< endl;
			else
				cout << "Model"
						<< fileName.substr(17,
								fileName.size() - 21) << "_"
						<< fileCount << "-" << extfileCount
						<< " file is produced" << endl;
		}

		//read the previous model
		ostringstream extmodel;
		ss.clear();
		ss.str("");
		if (fileCount == 0)
			ss << "Model"
					<< fileName.substr(17,
							fileName.size() - 21);
		else
			ss << "Model"
					<< fileName.substr(17, fileName.size() - 21)
					<< "_" << fileCount;
		if (extfileCount != 0)
			ss << "-" << extfileCount;
		ifstream extin_file(ss.str().c_str());
		extmodel << extin_file.rdbuf();
		string extModelStr = extmodel.str();
		extin_file.close();
		istringstream extiss(extModelStr);
		string extline;
		getline(extiss, extline);

		// read the previous SMT file.
		ostringstream extSMT;
		ss.clear();
		ss.str("");
		if (fileCount == 0)
			ss << "SMT"
					<< fileName.substr(17,
							fileName.size() - 21);
		else
			ss << "SMT"
					<< fileName.substr(17, fileName.size() - 21)
					<< "_" << fileCount;
		ss << "-" << extfileCount;
		ifstream extin_file_SMT(ss.str().c_str());
		extSMT << extin_file_SMT.rdbuf();
		string extSMTStr = extSMT.str();
		extin_file_SMT.close();

		//if the previous model is satisfiable, then make sure that we find a different value assignment
		if ((extline == "unsupported" || extline == "supported")
				&& param.SMTsolver == YICES)  	   //case: yices
			getline(extiss, extline);
		if (extline == "sat") {
			stringstream liness;
			string str_search = "; Check satisfiability";
			ss.clear(); //store the denial of the model in ss
			ss.str("");

			string CurVar = "";
			string CurVal = "";
			ss << "(assert (or ";
			while (getline(extiss, extline)) {
				//if a variable name is read, store it in curVar.
				if ((param.SMTsolver == CVC4
						|| param.SMTsolver == Z3)
						&& extline.find("(define-fun ")
								!= string::npos) {
					int StartPos = extline.find("(define-fun ");
					int EndPos = extline.find(" () ");
					CurVar = extline.substr(StartPos + 12,
							EndPos - StartPos - 12);
				} else if (param.SMTsolver == YICES
						&& extline.find("(= ")
								!= string::npos) {
					liness.clear();
					liness.str(extline);
					getline(liness, CurVar, ' ');
					getline(liness, CurVar, ' ');
				} else
					continue;

				//if it is a variable, store its value in curVal
				if ((param.SMTsolver == CVC4

						&& (extline.find(" Int ")
								!= string::npos
								|| extline.find(" Real ")
										!= string::npos))) {

					liness.clear();
					liness.str(extline);
					getline(liness, CurVal, ' ');
					getline(liness, CurVal, ' ');
					getline(liness, CurVal, ' ');
					getline(liness, CurVal, ' ');
					getline(liness, CurVal, ' ');
					if (CurVal[1] == '-') {
						getline(liness, CurVal, ' ');

						CurVal = "(- " + CurVal;
					}

				} else if ((param.SMTsolver == Z3
						&& (extline.find(" Int") != string::npos
								|| extline.find(" Real")
										!= string::npos))) {
					getline(extiss, extline);

					liness.clear();
					liness.str(extline);
					getline(liness, CurVal, ' ');
					getline(liness, CurVal, ' ');
					getline(liness, CurVal, ' ');
					getline(liness, CurVal, ' ');
					getline(liness, CurVal, ' ');
					if (CurVal[1] == '-') {
						getline(liness, CurVal, ' ');
						CurVal = CurVal.substr(0,
								CurVal.length() - 1);
						CurVal = "-" + CurVal;
					}
				} else if (param.SMTsolver == YICES
						&& extline.find(" true)")
								== string::npos
						&& extline.find(" false)")
								== string::npos) {
					getline(liness, CurVal, ' ');
					if (CurVal[1] == '-') {
						getline(liness, CurVal, ' ');

						CurVal = "(- " + CurVal;
					}
				}

				else
					continue;

				//Add assertions

				if (CurVar.substr(0, 1) == "|") {
					if (!isdigit(CurVar[1])
							&& CurVar.find("cspvar")
									== string::npos
							&& CurVar.find("required(")
									== string::npos
							&& (CurVar[1] != 'l'
									|| CurVar[2] != 'r')
							&& CurVar.find("cspdomain")
									== string::npos) {
						ss << " (distinct " << CurVar << " "
								<< CurVal.substr(0,
										CurVal.length() - 1)
								<< ")";
					}
				} else if (!isdigit(CurVar[0])
						&& CurVar.find("cspvar") == string::npos
						&& CurVar.find("required(")
								== string::npos
						&& (CurVar[0] != 'l' || CurVar[1] != 'r')
						&& CurVar.find("cspdomain")
								== string::npos) {
					ss << " (distinct " << CurVar << " "
							<< CurVal.substr(0,
									CurVal.length() - 1) << ")";
				}

			}
			extfileCount++;
			ss << "))\n; Check satisfiability";
			string str_replace = ss.str();
			size_t assertionPos = extSMTStr.find(str_search);

			extSMTStr.replace(assertionPos,
					string(str_search).length(), str_replace);

			ss.clear();
			ss.str("");
			if (fileCount == 0)
				ss << "SMT"
						<< fileName.substr(17,
								fileName.size() - 21);
			else
				ss << "SMT"
						<< fileName.substr(17,
								fileName.size() - 21) << "_"
						<< fileCount;
			ss << "-" << extfileCount;
			ofstream extout_file(ss.str().c_str());
			cerr << "writing SMT file: " << ss.str().c_str()
					<< endl;
			extout_file << extSMTStr;

		} else {
			cout << "-------------------------" << endl;
			// if (extline.find("(error ") != string::npos
			// 		|| line.find("unknown") != string::npos
			// 		|| line == "") {
			// 	cerr
			// 			<< " *** Error reported by SMT solver. See SMT solver's output "
			// 			<< "Model"
			// 			<< fileName.substr(17,
			// 					fileName.size() - 21);
			// 	if (fileCount != 0)
			// 		cerr << "_" << fileCount;
			// 	if (extfileCount != 0)
			// 		cerr << "-" << extfileCount;
			// 	cerr << ", and input file SMT"
			// 			<< fileName.substr(17,
			// 					fileName.size() - 21);
			// 	if (fileCount != 0)
			// 		cerr << "_" << fileCount;
			// 	if (extfileCount != 0)
			// 		cerr << "-" << extfileCount;
			// 	cerr << " ***" << endl;
			// 	exit(1);

			// }
			break;
		}

	} while (param.extmany == 0 || extfileCount < param.extmany);
}

bool parseSolverResults(string resultsFileName, vector<string>& resultAnswerSet)
{
	resultAnswerSet.clear();
	ifstream inputStream(resultsFileName);

	string satResult;
	std::getline(inputStream, satResult);

	if (satResult == "unsat")
	{
		return false;
	}

	// TODO support multi-line output
	string atomsList;
	std::getline(inputStream, atomsList);

	regex r ("\\(([^ ]*) true\\)");
	smatch match;
	string::const_iterator searchStart(atomsList.cbegin());
	while (regex_search(searchStart, atomsList.cend(), match, r))
	{
		searchStart = match.suffix().first;
		cout << "Found true atom: " << match[1] << endl;
		resultAnswerSet.insert(match[1].str());
	}
	// else
	// {
	// 	// TODO throw exception
	// }

	return true;
}

// TODO Move all SMT solver interfacing out of cmodels
// call EZSMT and SMT solver
void Cmodels::callSMTSolver() {
	if (param.extmany != 1)
		param.PrintExtAS = true;
	string fileName(param.dimacsFileName);
	string solverCommand = "";
	if (param.SMTsolver == CVC4)
		solverCommand = "$EZSMTPLUS/tools/cvc4 --lang smt --output-lang smtlib2.6 ";
	else if (param.SMTsolver == Z3)
		solverCommand = "$EZSMTPLUS/tools/z3 -smt2 ";
	else if (param.SMTsolver == YICES)
		solverCommand = "$EZSMTPLUS/tools/yices-smt2 ";
	stringstream ss;

	string smtFileName = "SMT" + fileName.substr(17);
	writeToSmtLibFile(smtFileName);

	// computeOneSMTModel(smtFileName, solverCommand, 0);

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


		for (auto smtAtom: resultAnswerSets)
		{
			// TODO continue
		}

		i++;
	} while (i == 1);

	// computing models
	// int fileCount = 0;
	// do {
	// 	ss.clear();
	// 	ss.str("");

	// 	// call SMT solver to compute one model
	// 	computeOneSMTModel(smtFileName, solverCommand, fileCount);
	// 	break;

		// //read the previous model
		// ostringstream model;
		// ss.clear();
		// ss.str("");
		// if (fileCount == 0)
		// 	ss << "Model" << fileName.substr(17, fileName.size() - 21);
		// else
		// 	ss << "Model" << fileName.substr(17, fileName.size() - 21)
		// 			<< "_" << fileCount;
		// ifstream in_file(ss.str().c_str());
		// model << in_file.rdbuf();
		// string ModelStr = model.str();
		// in_file.close();
		// istringstream iss(ModelStr);
		// string line;
		// getline(iss, line);
		// // read the previous SMT file.
		// ostringstream SMT;
		// ss.clear();
		// ss.str("");
		// if (fileCount == 0)
		// 	ss << "SMT" << fileName.substr(17, fileName.size() - 21);
		// else
		// 	ss << "SMT" << fileName.substr(17, fileName.size() - 21) << "_"
		// 			<< fileCount;
		// ifstream in_file_SMT(ss.str().c_str());

		// SMT << in_file_SMT.rdbuf();
		// string SMTStr = SMT.str();
		// in_file_SMT.close();

		// if ((line == "unsupported" || line == "supported")
		// 		&& param.SMTsolver == YICES)  	         //case: yices
		// 	getline(iss, line);



		// //if the previous model is satisfiable, then enumerate extended answer sets
		// if (line == "sat") {
		// 	if (param.extmany > 1 || param.extmany == 0) {
		// 		enumerateExtendedAnswerSets(fileName, solverCommand, fileCount, SMTStr, &iss);
		// 	}
		// } else {
		// 	//Report errors from SMT solvers
		// 	cout << "-------------------------" << endl;
		// 	if (line.find("(error ") != string::npos
		// 			|| line.find("unknown") != string::npos || line == "") {
		// 		cerr << " *** Error reported by SMT solver. See output "
		// 				<< "Model"
		// 				<< fileName.substr(17, fileName.size() - 21);
		// 		if (fileCount != 0)
		// 			cerr << "_" << fileCount;
		// 		cerr << ", and input file SMT"
		// 				<< fileName.substr(17, fileName.size() - 21);
		// 		if (fileCount != 0)
		// 			cerr << "_" << fileCount;
		// 		cerr << " ***" << endl;
		// 		exit(1);

		// 	}
		// }
		
	
	
		// // if the previous model is satisfiable, then add assertions so that new answer set to the
		// // modified problem is different from previous solutions.
		// iss.clear();
		// iss.seekg(0);
		// ss.clear();
		// ss.str("");
		// if (fileCount == 0)
		// 	ss << "SMT" << fileName.substr(17, fileName.size() - 21);
		// else
		// 	ss << "SMT" << fileName.substr(17, fileName.size() - 21) << "_"
		// 			<< fileCount;
		// ifstream in_file_SMT2(ss.str().c_str());
		// SMT.clear();
		// SMT.str("");
		// SMT << in_file_SMT2.rdbuf();
		// SMTStr = SMT.str();
		// in_file_SMT2.close();
		// getline(iss, line);
		// if ((line == "unsupported" || line == "supported")
		// 		&& param.SMTsolver == YICES)  	         //case: yices
		// 	getline(iss, line);
		// if (line == "sat") {
		// 	string str_search = "; Check satisfiability";
		// 	ss.clear(); //store the denial of the model in ss
		// 	ss.str("");
		// 	ss << "(assert (or ";
		// 	string CurVar = "";
		// 	while (getline(iss, line)) {

		// 		//if a variable name is read, store it in curVar.
		// 		if ((param.SMTsolver == CVC4 || param.SMTsolver == Z3)
		// 				&& line.find("(define-fun ") != string::npos) {
		// 			int StartPos = line.find("(define-fun ");
		// 			int EndPos = line.find(" () ");
		// 			CurVar = line.substr(StartPos + 12,
		// 					EndPos - StartPos - 12);
		// 		} else if (param.SMTsolver == YICES
		// 				&& line.find("(= ") != string::npos) {

		// 			int StartPos = line.find("(= ");
		// 			if (line.find(" true)") != string::npos) {
		// 				int EndPos = line.find(" true)");
		// 				CurVar = line.substr(StartPos + 3,
		// 						EndPos - StartPos - 3);
		// 			} else if (line.find(" false)") != string::npos) {
		// 				int EndPos = line.find(" false)");
		// 				CurVar = line.substr(StartPos + 3,
		// 						EndPos - StartPos - 3);
		// 			} else {
		// 				//It's not a regular atom, or "false)" and "true)" is pushed into the next line
		// 				//reset curVar
		// 				CurVar = "cspdomain";
		// 				continue;
		// 			}

		// 		} else if (param.SMTsolver == YICES
		// 				&& line.find("(=") != string::npos) {
		// 			//if a variable's name is too long, it will be on the next line in output
		// 			getline(iss, line);
		// 			CurVar = line;
		// 			getline(iss, line);
		// 		}

		// 		//if the variable is not level ranking variable
		// 		if (CurVar.find("required(") == string::npos
		// 				&& CurVar.find("cspvar") == string::npos
		// 				&& CurVar.find("cspdomain") == string::npos) {
		// 			// if the variable is asserted to be true
		// 			if (line.find(" true)") != string::npos) {
		// 				if (CurVar.substr(0, 1) == "|") {
		// 					if (!isdigit(CurVar[1]))
		// 						ss << "(not " << CurVar << ") ";
		// 				} else {
		// 					if (!isdigit(CurVar[0]))
		// 						ss << "(not |" << CurVar << "|) ";
		// 				}
		// 			}
		// 			// if the variable is asserted to be false
		// 			else if (line.find(" false)") != string::npos) {
		// 				if (CurVar.substr(0, 1) == "|") {
		// 					if (!isdigit(CurVar[1]))
		// 						ss << CurVar << " ";
		// 				} else {
		// 					if (!isdigit(CurVar[0]))
		// 						ss << "|" << CurVar << "| ";
		// 				}
		// 			}

		// 		}
		// 	}

		// 	//If there is no atoms that could possibly have a different truth value,
		// 	//then stop enumeration.
		// 	if (ss.str() == "(assert (or ") {
		// 		cout << "No more answer sets available." << endl;
		// 		fileCount++;
		// 		break;
		// 	}

		// 	ss << "))\n; Check satisfiability";
		// 	string str_replace = ss.str();
		// 	size_t assertionPos = SMTStr.find(str_search);
		// 	SMTStr.replace(assertionPos, string(str_search).length(),
		// 			str_replace);
		// 	fileCount++;
		// 	ss.clear();
		// 	ss.str("");
		// 	ss << "SMT" << fileName.substr(17, fileName.size() - 21) << "_"
		// 			<< fileCount;
		// 	ofstream out_file(ss.str().c_str());
		// 	cerr << "writing SMT file: " << ss.str().c_str() << endl;
		// 	out_file << SMTStr;
		// }

		// //if the previous model is unsatisfiable, then break.
		// else {

		// 	if (line != "unsat") {
		// 		cout << "No more answer sets available." << endl;
		// 		break;
		// 	}

		// 	if (line.find("(error ") != string::npos
		// 			|| line.find("unknown") != string::npos) {
		// 		cout << "-------------------------" << endl;
		// 		cerr << " *** Error reported by SMT solver. See output "
		// 				<< "Model"
		// 				<< fileName.substr(17, fileName.size() - 21);
		// 		if (fileCount != 0)
		// 			cerr << "_" << fileCount;
		// 		cerr << ", and input file SMT"
		// 				<< fileName.substr(17, fileName.size() - 21);
		// 		if (fileCount != 0)
		// 			cerr << "_" << fileCount;
		// 		cerr << " ***" << endl;
		// 		exit(1);

		// 	}

		// 	break;
		// }
	// } while (param.many == 0 || fileCount < param.many);

	// print results
	printSMTAnswerSets(0, fileName);

	return;
}

// parse SMT solvers' results and print answer sets
void Cmodels::printSMTAnswerSets(int fileCount, string fileName) {
	cout << "---------" << endl << "Number of answer sets: " << fileCount
			<< endl;
	stringstream ss;
	for (int c = 0; c < fileCount; c++) {
		//read the previous model
		ostringstream model;
		ss.clear();
		ss.str("");
		if (c == 0)
			ss << "Model" << fileName.substr(17, fileName.size() - 21);
		else
			ss << "Model" << fileName.substr(17, fileName.size() - 21)
					<< "_" << c;
		cout << "Answer: " << c + 1 << endl;
		ifstream in_file(ss.str().c_str());
		model << in_file.rdbuf();
		string ModelStr = model.str();
		in_file.close();
		istringstream iss(ModelStr);
		string line;
		getline(iss, line);

		if ((line == "unsupported" || line == "supported")
				&& param.SMTsolver == YICES)				//case: yices
			getline(iss, line);
		//if the model is satisfiable, then get the atoms interpreted as true.
		if (line == "sat") {
			ss.clear();
			ss.str("");
			ss << " Answer set:";
			string CurVar = "";
			string CurVal = "";
			while (getline(iss, line)) {
				//if a variable name is read, store it in curVar.
				if ((param.SMTsolver == CVC4 || param.SMTsolver == Z3)
						&& line.find("(define-fun ") != string::npos) {
					int StartPos = line.find("(define-fun ");
					int EndPos = line.find(" () ");
					CurVar = line.substr(StartPos + 12,
							EndPos - StartPos - 12);

				} else if (param.SMTsolver == YICES
						&& line.find("(= ") != string::npos) {

					int StartPos = line.find("(= ");
					if (line.find(" true)") != string::npos) {
						int EndPos = line.find(" true)");
						CurVar = line.substr(StartPos + 3,
								EndPos - StartPos - 3);
					} else if (line.find(" false)") != string::npos) {
						int EndPos = line.find(" false)");
						CurVar = line.substr(StartPos + 3,
								EndPos - StartPos - 3);
					} else {
						//It's not a regular atom, or "false)" and "true)" is pushed into the next line
						//reset curVar
						CurVar = "cspdomain";
						continue;
					}

				} else if (param.SMTsolver == YICES
						&& line.find("(=") != string::npos) {
					//if a variable's name is too long, it will be on the next line in output
					getline(iss, line);
					CurVar = line;
					getline(iss, line);
				}

				//if the variable is artessed to be true
				if (line.find(" true)") != string::npos) {
					if (CurVar.substr(0, 1) == "|") {
						if (!isdigit(CurVar[1])
								&& CurVar.find("cspvar") == string::npos
								&& CurVar.find("required(") == string::npos
								&& CurVar.find("cspdomain") == string::npos)
							ss << " "
									<< CurVar.substr(1,
											CurVar.length() - 2);
					} else {
						if (!isdigit(CurVar[0])
								&& CurVar.find("cspvar") == string::npos
								&& CurVar.find("required(") == string::npos
								&& CurVar.find("cspdomain") == string::npos)
							ss << " " << CurVar;
					}
				}
			}

			cout << ss.str() << endl;
		} else
			return;

		//print extended answer sets when being invoked with -PrintExtAS flag
		if (param.PrintExtAS == true) {
			string CurVar = "";
			string CurVal = "";
			string temp = "";
			int c2 = 0;
			do {

				//read the previous model
				ostringstream model;
				ss.clear();
				ss.str("");
				ss << "Model" << fileName.substr(17, fileName.size() - 21);
				if (c != 0)
					ss << "_" << c;
				if (c2 != 0)
					ss << "-" << c2;
				ifstream in_file2(ss.str().c_str());

				if (in_file2) {
					ss.clear();
					ss.str("");
					cout << " Value Assignment " << c2 + 1 << ":" << endl
							<< "  ";
					model << in_file2.rdbuf();
					string ModelStr = model.str();
					in_file2.close();
					istringstream extiss(ModelStr);
					string line;
					getline(extiss, line);
					if ((line == "unsupported" || line == "supported")
							&& param.SMTsolver == YICES)	//case: yices
						getline(extiss, line);
					//if the model is satisfiable, then print
					if (line == "sat") {
						stringstream liness;
						liness.clear();
						liness.str("");
						while (getline(extiss, line)) {
							//if a variable name is read, store it in curVar.
							if ((param.SMTsolver == CVC4
									|| param.SMTsolver == Z3)
									&& line.find("(define-fun ")
											!= string::npos) {
								int StartPos = line.find("(define-fun ");
								int EndPos = line.find(" () ");
								CurVar = line.substr(StartPos + 12,
										EndPos - StartPos - 12);
							} else if (param.SMTsolver == YICES
									&& line.find("(= ") != string::npos) {
								liness.clear();
								liness.str(line);
								getline(liness, CurVar, ' ');
								getline(liness, CurVar, ' ');
							} else
								continue;

							//if it is a variable, store its value in curVal
							if ((param.SMTsolver == CVC4

									&& (line.find(" Int ") != string::npos
											|| line.find(" Real ")
													!= string::npos))) {

								liness.clear();
								liness.str(line);
								getline(liness, CurVal, ' ');
								getline(liness, CurVal, ' ');
								getline(liness, CurVal, ' ');
								getline(liness, CurVal, ' ');
								getline(liness, CurVal, ' ');

								//if it is a positive real number
								if (CurVal[0] == '(' && CurVal[1] == '/') {
									getline(liness, CurVal, ' ');
									temp = CurVal;
									getline(liness, CurVal, ')');
									CurVal = "(/ " + temp + " " + CurVal
											+ "))";
								}

								//if it is a negative number
								if (CurVal[1] == '-') {

									getline(liness, CurVal, ' ');

									//if it is a negative real number
									if (CurVal[0] == '('
											&& CurVal[1] == '/') {
										getline(liness, CurVal, ' ');
										temp = CurVal;
										getline(liness, CurVal, ')');
										CurVal = "(/ " + temp + " " + CurVal
												+ ")))";
									}

									CurVal = CurVal.substr(0,
											CurVal.length() - 1);

									CurVal = "- " + CurVal;

								}
							} else if ((param.SMTsolver == Z3
									&& (line.find(" Int") != string::npos
											|| line.find(" Real")
													!= string::npos))) {
								getline(extiss, line);

								liness.clear();
								liness.str(line);
								getline(liness, CurVal, ' ');
								getline(liness, CurVal, ' ');
								getline(liness, CurVal, ' ');
								getline(liness, CurVal, ' ');
								getline(liness, CurVal, ' ');

								//if it is a positive real number
								if (CurVal[0] == '(' && CurVal[1] == '/') {
									getline(liness, CurVal, ' ');
									temp = CurVal;
									getline(liness, CurVal, ')');
									CurVal = "(/ " + temp + " " + CurVal
											+ "))";
								}

								//if it is a negative number
								if (CurVal[1] == '-') {
									getline(liness, CurVal, ' ');

									//if it is a negative real number
									if (CurVal[0] == '('
											&& CurVal[1] == '/') {
										getline(liness, CurVal, ' ');
										temp = CurVal;
										getline(liness, CurVal, ')');
										CurVal = "(/ " + temp + " " + CurVal
												+ ")))";
									}

									CurVal = CurVal.substr(0,
											CurVal.length() - 1);

									CurVal = "-" + CurVal;
								}
							} else if (param.SMTsolver == YICES
									&& line.find(" true)") == string::npos
									&& line.find(" false)")
											== string::npos) {
								getline(liness, CurVal, ' ');

								//if it is a real number
								if (CurVal[0] == '(' && CurVal[1] == '/') {
									getline(liness, CurVal, ' ');
									temp = CurVal;

									//if it is a negative real number
									if (temp[0] == '(' && temp[1] == '-') {

										getline(liness, CurVal, ' ');
										temp = temp + CurVal;
									}
									getline(liness, CurVal, ')');

									CurVal = "(/ " + temp + " " + CurVal
											+ "))";

								}

								//if it is a negative integer
								if (CurVal[1] == '-') {
									getline(liness, CurVal, ' ');
									CurVal = CurVal.substr(0,
											CurVal.length() - 1);
									CurVal = "-" + CurVal;
								}
							} else {

								continue;
							}

							//print CurVar = CurVal;
							if (CurVar.substr(0, 1) == "|") {
								if (!isdigit(CurVar[1])
										&& CurVar.find("cspvar")
												== string::npos
										&& CurVar.find("required(")
												== string::npos
										&& (CurVar[1] != 'l'
												|| CurVar[2] != 'r')
										&& CurVar.find("cspdomain")
												== string::npos) {
									ss << " "
											<< CurVar.substr(1,
													CurVar.length() - 2);
									ss << " = "
											<< CurVal.substr(0,
													CurVal.length() - 1)
											<< ";";
								}
							} else if (!isdigit(CurVar[0])
									&& CurVar.find("cspvar") == string::npos
									&& CurVar.find("required(")
											== string::npos
									&& (CurVar[0] != 'l' || CurVar[1] != 'r')
									&& CurVar.find("cspdomain")
											== string::npos) {
								ss << " " << CurVar;
								ss << " = "
										<< CurVal.substr(0,
												CurVal.length() - 1) << ";";
							}

						}

						cout << ss.str() << endl;
						c2++;

					} else
						break;
				} else
					break;
			} while (true);

		}

	}

	return;
}

void Cmodels::cmodels() {

	Result ret = (Result) UNKNOWN;
	bool programempty = false;
	ret = preprocessing(programempty);
	switch (ret) {
	case SAT: {
		output.sat = SAT;
		output.numSolutions++;
		if (!programempty)
			output.print_wfm();
		else {
			cerr << "Program is empty." << endl;
			//empty set is solution
			output.start_output();
			output.end_output();
		}
		return;
	}
	case UNSAT: {
		output.sat = UNSAT;
		output.false_output();
		return;
	}
	}
	if (param.sys == DIMACS_PRODUCE || param.sys == CASP_DIMACS_PRODUCE) {
		cerr << param.dimacsFileName << " file is produced" << endl;

		return;
	} else if (param.sys == LEVEL_RANKING || param.sys == LEVEL_RANKING_STRONG
			|| param.sys == SCC_LEVEL_RANKING
			|| param.sys == SCC_LEVEL_RANKING_STRONG) {

		callSMTSolver();
	} else {
		cerr << "Please specify the type of level rankings.";
		cerr << "Available options: -levelRanking -levelRankingStrong -SCClevelRanking -SCClevelRankingStrong" << endl;
	}

	// //cleans up if some files were created during the work
	// clean();

}



void Cmodels::eraseFalseAtomsFromClauses() {
	list<Atom*> temp;
	long prevCmId = program.cmodelsAtomsFromThisId;
	long numItr = 0;
	long id = 0;
	program.cmodelsAtomsFromThisId = 0;
	copyVectorToList(program.atoms, temp);
	list<Atom*>::iterator itrA = temp.begin();
	while (itrA != temp.end()) {
		if ((*itrA)->Bneg && (*itrA)->id != false_atom->id) {
			delete (*itrA);
			itrA = temp.erase(itrA);
		} else {
			id++;
			(*itrA)->id = id;
			itrA++;
			if (numItr < prevCmId)
				program.cmodelsAtomsFromThisId++;

		}
		numItr++;

	}
	copyListToVector(temp, program.atoms);
	program.number_of_atoms = program.atoms.size();
}
//
//removes files created by cmodels at the run
//
inline void Cmodels::clean() {
	if (!param.keep && param.sys != DIMACS_PRODUCE
			&& param.sys != CASP_DIMACS_PRODUCE
			&& param.sys != SCC_LEVEL_RANKING && param.sys != LEVEL_RANKING
			&& param.sys != SCC_LEVEL_RANKING_STRONG && param.sys != LEVEL_RANKING_STRONG) {
		unlink(param.dimacsFileName);
		unlink(param.solverOutputFileName);
	}
}

Cmodels::~Cmodels() {

}

//
//returns false if we can skip the rule since 
//the not part atom is in positive part of WFS
//
bool Cmodels::walk_nbody_to_add_body(Rule *r) {

	if (r->type == BASICRULE) {
		BasicRule * rr = (BasicRule*) r;
		for (Atom **a = rr->nbody; a != rr->nend; a++) {
			if ((*a)->Bpos || (*a)->computeTrue || (*a)->computeTrue0)
				return false;
			else if ((*a)->Bneg) {
				;
			} else
				api->add_body((*a), false);
		}

	} else if (r->type == CHOICERULE) {
		ChoiceRule * rr = (ChoiceRule*) r;
		for (Atom **a = rr->nbody; a != rr->nend; a++) {
			if ((*a)->Bpos || (*a)->computeTrue || (*a)->computeTrue0)
				return false;
			else if ((*a)->Bneg) {
				;
			} else
				api->add_body((*a), false);
		}

	} else if (r->type == DISJUNCTIONRULE) {
		DisjunctionRule * rr = (DisjunctionRule*) r;
		for (Atom **a = rr->nbody; a != rr->nend; a++) {
			if ((*a)->Bpos || (*a)->computeTrue || (*a)->computeTrue0)
				return false;
			else if ((*a)->Bneg) {
				;
			} else
				api->add_body((*a), false);
		}

	}
	return true;
}

bool Cmodels::walk_pbody_to_add_body(Rule * r) {
	if (r->type == BASICRULE) {
		BasicRule * rr = (BasicRule*) r;
		for (Atom **a = rr->pbody; a != rr->pend; a++) {
			//ASSAT
			//if p:-G if p belongs to G the rule may be taken away from a program
			if ((*rr->head).id == (*a)->id)
				return false;
			if ((*a)->Bneg)
				return false;
			else
				api->add_body((*a), true);
		}

	} else if (r->type == CHOICERULE) {
		ChoiceRule * rr = (ChoiceRule*) r;
		for (Atom **a = rr->pbody; a != rr->pend; a++) {
			if ((*a)->Bneg)
				return false;
			else
				api->add_body((*a), true);

		}

	} else if (r->type == DISJUNCTIONRULE) {
		DisjunctionRule * rr = (DisjunctionRule*) r;
		for (Atom **a = rr->pbody; a != rr->pend; a++) {
			//	  if((*a)->Bneg)
			//return false;
			//else
			//ASSAT
			//if ..p..:-G if p belongs to G the rule may be taken away from a program
			//done at the point when we read in the program
			for (Atom **h = rr->head; h != rr->hend; h++) {
				if ((*h)->id == (*a)->id)
					return false;
			}

			if ((*a)->Bneg)
				return false;
			else
				api->add_body((*a), true);

		}

	}

	return true;
}
//
//thrus out Bneg's in Pos part and Bpos in Neg part
// while when it encounters true, it lowers atleast boder
//
void Cmodels::walk_nbody_constraintrule_to_add_body(ConstraintRule *r) {

	for (Atom **a = r->nbody; a != r->nend; a++) {

		if ((*a)->Bpos || (*a)->computeTrue || (*a)->computeTrue0) {
			;
		} else if ((*a)->Bneg) {
			r->atleast--;
		} else
			api->add_body((*a), false);

	}
	return;
}
void Cmodels::walk_pbody_constraintrule_to_add_body(ConstraintRule * r) {
	for (Atom **a = r->pbody; a != r->pend; a++) {
		//ASSAT
		//if p:-G if p belongs to G the rule may be taken away from a program
		if ((*r->head).id == (*a)->id) {
			;
		} else if ((*a)->Bneg) {
			;
		} else {
			api->add_body((*a), true);	//(ConstraintRule*) r->atleast--;
		}
	}
	return;
}
//
//thrus out Bneg's in Pos part and Bpos in Neg part
// while when it encounters true, it lowers atleast boder
//
void Cmodels::walk_body_weightrule_to_add_body(WeightRule *r) {

	for (Atom **a = r->body; a != r->end; a++) {
		if (!r->aux[a - r->body].positive) {	//if this is nbody part
			if ((*a)->Bpos) {
				;
			} else if ((*a)->Bneg) {
				Weight weight = r->aux[a - r->body].weight;
				r->atleast -= weight;
			} else
				api->add_body_LEGACY((*a), r->aux[a - r->body].weight, false);
		} else { //this is pbody part
			if ((*a)->Bneg) {
				;
			} else if ((*a)->Bpos) {
				api->add_body_LEGACY((*a), r->aux[a - r->body].weight, true);
			} else {
				api->add_body_LEGACY((*a), r->aux[a - r->body].weight, true);
			}
		}
	}
	return;
}
bool Cmodels::walk_to_add_head(DisjunctionRule* r) {
	//do not add negative heads
	for (Atom **a = r->head; a != r->hend; a++) {
		if (!(*a)->Bneg)
			api->add_head((*a));
		if ((*a)->Bpos)
			return false; //if one of the atoms is Bpos in disj head
		//then we can thru out the rule
	}
	return true;
}
inline void Cmodels::add_fact_rule(Atom *a) {
	//add nested rule for supportednes of this atom
	assert(a);
	NestedRule *rcopy = new NestedRule();
	rcopy->type = BASICRULE;
	rcopy->allocateRule(1, 0, 0);
	a->addToRuleList(rcopy);
	rcopy->addHead(0, a);
}
//returns true if program is nondisjuntive
//if program is disjunctive return false
bool Cmodels::translate_all_to_nested_rules() {
	bool disjRuleAdded = false; //return negated value
	true_atom = api->new_atom();
	true_atom->Bpos = true;
	if (program.false_atom) {
		false_atom = program.false_atom;
	} else {
		false_atom = api->new_atom();
		false_atom->Bneg = true;
	}

	//create simplification using wellfounded semantics
	for (long indA = 0; indA < program.atoms.size(); indA++) {
		program.atoms[indA]->headof = 0;
		if (program.atoms[indA]->Bpos) {
			program.atoms[indA]->headof++;
			if (param.verifyMethod == MIN)
				add_fact_rule(program.atoms[indA]);
		}
	}
	//
	//traverse rules
	//we erase the rule from a list and free the memory after we
	//finished working on the rule
	Rule *rule;
	//  for(long indR=0; indR<program.rules.size(); indR++){
	for (list<Rule*>::iterator itrR = program.rules.begin();
			itrR != program.rules.end(); itrR++) {
		rule = (*itrR);
		//	if(rule->satUUn!=SAT){//SAT is specified at WFM

		api->rule_reset();
		switch (rule->type) {
		//seems like there is nothing but basic and constarint rules
		//after lparse so we will see
		//but for now those are the cases we translate to basic rules
		// and store them in program.basicRules

		//case BASICRULE is taken care at reading part
		//since we don't need to translate them but they are created and placed
		//to program-basicrule right away at creation

		case BASICRULE: {

			BasicRule *r = (BasicRule *) rule;
			assert(r);

			//
			//if someone in the body is Bneg and in pos side
			//or if head is already known to be positive
			//then we thru out the rule
			//
			//creates api  head, pbody, nbody copy of a rule
			if (r->head->Bpos || !walk_nbody_to_add_body(r)
					|| !walk_pbody_to_add_body(r)) {
				api->rule_reset();
				break;
			}
			if (r->head->Bneg) {//if the rule is constraint then we replace it by
				//false_atom
				api->add_head(false_atom);

			} else
				api->add_head(r->head);
			Atom* at = api->headAtom(0);
			NestedRule *rcopy = new NestedRule();
			//copies rule from api head, pbody, nbody into rcopy
			rcopy->initRuleFromApi(api, BASICRULE);
			rcopy->finishRule();
			api->headAtom(0)->addToRuleList(rcopy);

			//  if(rcopy->head[0]->Bneg){
			//rcopy->print();
			//r->print();
			//}
			program.number_of_nestedRules++;
			break;
		}

		case DISJUNCTIONRULE: {
			program.basic = false;

			DisjunctionRule *r = (DisjunctionRule *) rule;
			//r->print();
			//
			//if someone in the body is Bneg and in pos side
			//then we thru out the rule
			//
			if (!walk_nbody_to_add_body(r) || !walk_pbody_to_add_body(r)
					|| !walk_to_add_head(r)) {
				api->rule_reset();
				break;
			}
			if (api->sizeHead() == 0) {	  //this is a constraint
				//we add a clause Bneg:-Body;
				api->add_head(false_atom);

			}
			//createn of api copy of a rule is just completed
			NestedRule *rcopy = new NestedRule();
			//copies rule from api head, pbody, nbody into rcopy
			rcopy->initRuleFromApi(api, DISJUNCTIONRULE);
			rcopy->finishRule();
			disjRuleAdded = true;

			program.number_of_nestedRules++;
			//adds a rule to the list of each atom in the head
			for (int i = 0; i < api->sizeHead(); i++) {
				rcopy->head[i]->addToRuleList(rcopy);

			}
			break;
		}

		case CONSTRAINTRULE: {

			ConstraintRule *r = (ConstraintRule *) rule;

			//if head atom of the rule is already known
			//to be positive we thru it out
			if (r->head->Bpos)
				break;
			if (r->head->Bneg)//if the rule is constraint then we replace it by
				//false_atom
				api->add_head(false_atom);
			else
				api->add_head(r->head);

			walk_nbody_constraintrule_to_add_body(r);
			walk_pbody_constraintrule_to_add_body(r);

			long num = api->sizeNbody() + api->sizePbody();

			if (r->atleast < 0)
				r->atleast = 0;

			//
			//we simply thru out the rule because it is of the form p:-false
			//
			if (r->atleast > num) {
				break;
			}
			switch (r->atleast) {

			//n==0 then A<-0{..} will be simply true clause A.
			case 0: {
				assert(api->sizeHead() == 1);
				Atom *acopy = api->headAtom(0);
				acopy->headof++;
				if (param.verifyMethod == MIN)
					add_fact_rule(acopy);
				acopy->Bpos = true;
				assert(!acopy->Bneg);
				break;
			}
			case 1: {
				assert(api->sizeHead() == 1);

				//out of A<-1{e1,...,e2}. we will generate A<-e1 ...A<-e2
				//we are craeting rules A<-not ei now
				//
				for (int j = 0; j < api->sizeNbody(); j++) {
					NestedRule *rcopy = new NestedRule();
					rcopy->type = BASICRULE;
					api->headAtom(0)->addToRuleList(rcopy);
					rcopy->allocateRule(1, 1, 0);
					rcopy->addHead(0, api->headAtom(0));
					rcopy->addNbody(0, api->nbodyAtom(j));
					rcopy->finishRule();

					program.number_of_nestedRules++;

				}
				//we are craeting rules A<- ei now
				//
				for (int j = 0; j < api->sizePbody(); j++) {
					NestedRule *rcopy = new NestedRule();
					rcopy->type = BASICRULE;
					api->headAtom(0)->addToRuleList(rcopy);
					rcopy->allocateRule(1, 0, 1);
					rcopy->addHead(0, api->headAtom(0));
					rcopy->addPbody(0, api->pbodyAtom(j));
					rcopy->finishRule();

					program.number_of_nestedRules++;

				}

				break;
			}
			case 2: {
				assert(api->sizeHead() == 1);

				//out of A<-2{e1,...,en}. we will generate A<-e1,e2 ...A<-en-1, en-1
				//we are craeting rules A<-not ei, not ej i!=j now
				//
				for (int j = 0; j < api->sizeNbody() - 1; j++) {
					for (int j1 = j + 1; j1 < api->sizeNbody(); j1++) {
						NestedRule *rcopy = new NestedRule();
						rcopy->type = BASICRULE;
						api->headAtom(0)->addToRuleList(rcopy);
						rcopy->allocateRule(1, 2, 0);
						rcopy->addHead(0, api->headAtom(0));
						rcopy->addNbody(0, api->nbodyAtom(j));
						rcopy->addNbody(1, api->nbodyAtom(j1));
						rcopy->finishRule();

						program.number_of_nestedRules++;

					}
				}
				//we are craeting rules A<- ei,ej i!=j now
				//
				for (int j = 0; j < api->sizePbody() - 1; j++) {
					for (int j1 = j + 1; j1 < api->sizePbody(); j1++) {
						NestedRule *rcopy = new NestedRule();
						rcopy->type = BASICRULE;
						api->headAtom(0)->addToRuleList(rcopy);
						rcopy->allocateRule(1, 0, 2);
						rcopy->addHead(0, api->headAtom(0));
						rcopy->addPbody(0, api->pbodyAtom(j));
						rcopy->addPbody(1, api->pbodyAtom(j1));
						rcopy->finishRule();

						program.number_of_nestedRules++;

					}
				}
				//now we are creating A <- ei, not ej

				//we are craeting rules A<- ei,ej i!=j now
				//
				for (int j = 0; j < api->sizePbody(); j++) {
					for (int j1 = 0; j1 < api->sizeNbody(); j1++) {
						NestedRule *rcopy = new NestedRule();
						rcopy->type = BASICRULE;
						api->headAtom(0)->addToRuleList(rcopy);
						rcopy->allocateRule(1, 1, 1);
						rcopy->addHead(0, api->headAtom(0));
						rcopy->addNbody(0, api->nbodyAtom(j1));
						rcopy->addPbody(0, api->pbodyAtom(j));
						rcopy->finishRule();

						program.number_of_nestedRules++;

					}
				}
				api->rule_reset();
				break;
			}

			default: {
				assert(api->sizeHead() == 1);
				//case 4
				if (r->atleast == num) {
					NestedRule *rcopy = new NestedRule();
					rcopy->type = BASICRULE;
					api->headAtom(0)->addToRuleList(rcopy);

					rcopy->initRuleFromApi(api, BASICRULE);

					rcopy->finishRule();
					program.number_of_nestedRules++;

				} else
				//case 5
				if (r->atleast == num - 1) {

					for (int i = 0; i < api->sizeNbody(); i++) {

						NestedRule *rcopy = new NestedRule();
						rcopy->type = BASICRULE;
						api->headAtom(0)->addToRuleList(rcopy);

						program.number_of_nestedRules++;
						rcopy->allocateRule(1, api->sizeNbody() - 1,
								api->sizePbody());
						rcopy->addHead(0, api->headAtom(0));
						for (int j = 0; j < api->sizeNbody(); j++) {
							if (j < i)
								rcopy->addNbody(j, api->nbodyAtom(j));
							if (j > i)
								rcopy->addNbody(j - 1, api->nbodyAtom(j));
						}
						for (int j = 0; j < api->sizePbody(); j++) {
							rcopy->addPbody(j, api->pbodyAtom(j));
						}
						rcopy->finishRule();
					}

					for (int i = 0; i < api->sizePbody(); i++) {

						NestedRule *rcopy = new NestedRule();

						program.number_of_nestedRules++;

						rcopy->type = BASICRULE;
						api->headAtom(0)->addToRuleList(rcopy);

						rcopy->allocateRule(1, api->sizeNbody(),
								api->sizePbody() - 1);
						rcopy->addHead(0, api->headAtom(0));

						for (int j = 0; j < api->sizePbody(); j++) {
							if (j < i)
								rcopy->addPbody(j, api->pbodyAtom(j));
							if (j > i)
								rcopy->addPbody(j - 1, api->pbodyAtom(j));
						}
						for (int j = 0; j < api->sizeNbody(); j++) {
							rcopy->addNbody(j, api->nbodyAtom(j));
						}
						rcopy->finishRule();
					}
				} else {
					//	 "case 6"
					rec_buf_atoms = new Atom **[num + 1];

					for (int k = 0; k <= num; k++) {
						rec_buf_atoms[k] = new Atom*[r->atleast + 1];
					}

					for (int n = r->atleast; n >= 0; n--) {
						for (int m = num - r->atleast + n; m >= 0; m--) {
							rec_buf_atoms[m][n] = 0; //here we create
						}

					}

					//an aux atom for each rule of type t->atleast{a1 ...anum}

					//here we want to specify the relationships between
					//the auxilary atoms we just created, these aux
					//atoms stands each for the specific rule.
					//and so basically we have following relations:
					//rule[n,m], where m is num, n is r->atleast

					//rule[n,m]:-a1,r[n-1,m-1]
					//rule[n,m]:-r[n,m-1]

					// rec_buf_atoms[num-1][r->atleast] is actually r->head

					//we want to add relationships here

					for (int m = num - r->atleast; m >= 0; m--) {
						rec_buf_atoms[m][0] = true_atom;

					}

					for (int n = r->atleast; n >= 1; n--) {
						for (int m = num - r->atleast + n; m >= 0; m--) {

							if (n > m) {

								if (n == m + 1) {
									if (!rec_buf_atoms[m][n]) {
										rec_buf_atoms[m][n] = false_atom;

									}

								}

							} else { //third rule where we create two rules
								//for each rule
								// add_rule_1;
								// [L<=S] = (c_n,[L-1<=S'])

								NestedRule *rb = new NestedRule();
								rb->type = BASICRULE;
								if (!rec_buf_atoms[m][n]) {
									rec_buf_atoms[m][n] = api->new_atom();

								}
								Atom * acopy = rec_buf_atoms[m][n];
								acopy->addToRuleList(rb);

								program.number_of_nestedRules++;

								rb->allocateRule(1, 0, 1);
								rb->addHead(0, acopy);
								if (n == m + 1) {
									if (!rec_buf_atoms[m][n]) {
										rec_buf_atoms[m][n] = false_atom;

									}

								}
								if (!rec_buf_atoms[m - 1][n]) {
									if (n == m)
										rec_buf_atoms[m - 1][n] = false_atom;
									else
										rec_buf_atoms[m - 1][n] =
												api->new_atom();

								}
								rb->addPbody(0, rec_buf_atoms[m - 1][n]);
								rb->finishRule();
								// add_rule;
								//[L<=S] = ([L<=S'])
								NestedRule *rcopy1 = new NestedRule();
								rcopy1->type = BASICRULE;
								acopy = rec_buf_atoms[m][n];
								acopy->addToRuleList(rcopy1);

								program.number_of_nestedRules++;

								if (!rec_buf_atoms[m - 1][n - 1]) {
									rec_buf_atoms[m - 1][n - 1] =
											api->new_atom();

								}

								int counter1 = num - m;
								if (counter1 < api->sizeNbody()) {
									rcopy1->allocateRule(1, 1, 1);
									rcopy1->addNbody(0,
											api->nbodyAtom(counter1));
									rcopy1->addPbody(0,
											rec_buf_atoms[m - 1][n - 1]);
								} else {
									rcopy1->allocateRule(1, 0, 2);
									int pcounter1 = -api->sizeNbody()
											+ counter1;
									rcopy1->addPbody(0,
											api->pbodyAtom(pcounter1));
									rcopy1->addPbody(1,
											rec_buf_atoms[m - 1][n - 1]);
								}
								rcopy1->addHead(0, acopy);
								rcopy1->finishRule();
							}

						}

					}

					NestedRule *rc = new NestedRule();
					Atom * acopy = r->head;
					acopy->addToRuleList(rc);

					program.number_of_nestedRules++;
					rc->allocateRule(1, 0, 1);
					rc->addHead(0, acopy);
					rc->addPbody(0, rec_buf_atoms[num][r->atleast]);
					rc->finishRule();
				}

			}

			}
			break;
		}

		case WEIGHTRULE: {
			WeightRule *r = (WeightRule *) rule;
			//if the head is known to be positive already
			//we through the rule out
			if (r->head->Bpos)
				break;
			if (r->head->Bneg)//if the rule is constraint then we replace it by
				//false_atom
				api->add_head(false_atom);
			else
				api->add_head(r->head);

			api->add_head(r->head);
			//
			//if someone in the body in pos part Bpos then atleast-- weight(Bpos)
			//and we remove him from the body same for neg and Bneg
			//
			walk_body_weightrule_to_add_body(r);

			int num = api->sizePbody();
			if ((long) r->atleast <= 0)
				r->atleast = 0;

			//
			//we simply thru out the rule because it is of the form p:-false
			//
			Weight sumweights = api->totalweight(api->pbody);

			if (r->atleast > sumweights) {

				; //EXIT IN THE END CASE
			} else if (r->atleast == 0) {

				//n==0 then A<-0{..} will be simply true clause A.
				assert(api->sizeHead() == 1);
				Atom *acopy = api->headAtom(0);
				acopy->headof++;
				if (param.verifyMethod == MIN)
					add_fact_rule(acopy);
				acopy->Bpos = true;
			} else { //recursive case

				rec_weight_rule(sumweights, num, r->head, r->atleast, 0);
				api->wrmem.clearAll();
			}

			api->rule_reset();
			break;
		}

			//choice rule translation to basic rule
			//{p,q} <- Body

			//we can write:
			//q <- Body, q
			//p <- Body, p.

		case CHOICERULE: {
			program.basic = false;

			//copy from copy
			ChoiceRule *r = (ChoiceRule *) rule;

			if (!(r->head->Bneg || r->head->Bpos))
				api->add_head(r->head);

			//
			//if all heads are specified by WFS then we can go on here
			if (!api->sizeHead()) {
				break;
			}
			if (!walk_nbody_to_add_body(r) || !walk_pbody_to_add_body(r)) {
				break;
			}

			//if the body does not exist
			//then h v -h where h is one of the head atoms
			// in choice rule will be created
			// which will be tautology in clauses
			// but we need to take care, and assign
			// h->headoff++, not to create completion h<->F
			// later
			long heads = api->sizeHead();
			//if the body is empty
			if (api->sizeNbody() + api->sizePbody() == 0) {
				for (int i = 0; i < heads; i++) {
					//here we create a tautological clause and avoid
					//creating a rule as we won"t need it anywhere
					//atoms specified by such rules cannot
					//be part of any circle

					Atom *acopy = api->headAtom(i);
					//already either is a fact or negation so no need to add
					//the following clause
					if (!(acopy->Bpos || acopy->Bneg)) {
						acopy->headof++;
						acopy->choiceruleSpecified = true;
						//we add a nested rule since otherwise
						//completion is not computed properly!
						//			  createDoubleClause(acopy,acopy,true,false);
					}
				}
			}
			//	    else{
			//we will creat  as many basic rules as there heads
			for (int i = 0; i < heads; i++) {

				bool flag = false;
				//if it is specified as positive already
				//we skip the rule
				if (api->headAtom(i)->Bpos)
					flag = true;
				//if the current head occurs in pbody we skip the rule
				if (!flag)
					for (int j = 0; j < api->sizePbody(); j++) {
						if (api->headAtom(i) == api->pbodyAtom(j))
							flag = true;
					}
				if (!flag) {
					NestedRule *rcopy = new NestedRule();

					program.number_of_nestedRules++;
					Atom *acopy = api->headAtom(i);
					acopy->addToRuleList(rcopy);

					rcopy->allocateRule(1, api->sizeNbody(), api->sizePbody(),
							1);
					rcopy->addHead(0, acopy);
					rcopy->addNNbody(0, acopy);
					for (int k = 0; k < api->sizeNbody(); k++) {
						rcopy->addNbody(k, api->nbodyAtom(k));

					}
					for (int k = 0; k < api->sizePbody(); k++) {
						rcopy->addPbody(k, api->pbodyAtom(k));
					}
					rcopy->finishRule();
				}
			}
			// }
			break;

		}

		default:
			break;

		}
		//	}
		//
		// we delete a rule as at the moment we created
		// nested rule and added it to another list
		delete rule;

	}
	program.rules.clear();
	api->rule_reset();

	program.cmodelsAtomsFromThisId = program.number_of_atoms;
	return (!disjRuleAdded);

}

inline void Cmodels::resetCompApi() {
	api->comp_reset();
}

void Cmodels::createCompletion() {
	// we will start from program.false_atom since we are going
	//to work differently with it
	// we will find the situations such that _false<-int1.
	//                                       int1<-...hello_...
	// it is eq to false<-...hello_...
	// so in all the atoms like int1 we will put the flag atom->false_atom = true and build   // completion respectivly
	//

	//we go thru all the rules and if we note situation that
	//head atom is false_atom and it is body is single positive atom we mark the body
	//as a false atom as well
	//

	long curAtomsSize = program.atoms.size();
	for (long indA = 0; indA < curAtomsSize; indA++) {
		Atom *curAtom = program.atoms[indA];

		//if the atom has to be processed as a false one
		//lets say we had a situation such that _false<-int1
		//                                      int1<-...hello_...
		//it is eq to false<-...hello_...

		if (curAtom->Bneg && curAtom->nestedRules.size() > 0) {
			createFalseHeadClauses(curAtom);
		} else if (curAtom->Bpos) {
			//do nothing and lets go to the other atom -
			//we take care of this in the end when we build clauses
		} else {

			//if the are no rules with this atom in the head
			if (curAtom->nestedRules.empty()) {
				//do nothing and lets go to the other atom -
				//we take care of this in the end when we build clauses

			} else {

				Completion *comp = new Completion();
				comp->eq = IMPL;
				NestedRule* cr;
				if (curAtom->nestedRules.size() == 1) {	//only one rule then completion
					//is build from this disjunctive rule

					cr = curAtom->nestedRules.front();

					createNestedRuleBodyAClause(cr);
					if (!curAtom->choiceruleSpecified) {
						//if the atom is choice rule specified then it is of the form a:-not not a; and we added the clause accourdingly by now
						//changes for 3.71
						//if it is just a single rule we do not mark a completion!
						//
						comp->connector = AND;

						comp->head = curAtom;
						for (Atom **a = cr->head; a != cr->hend; a++) {
							if ((*a)->id != curAtom->id)
								api->add_body((*a), false);
						}
						placeToApi(cr->nbody, cr->nend, false);
						placeToApi(cr->pbody, cr->nnend, true);
						comp->initCompletionNbodyFromApi(api);
						resetApi();
						program.completions.push_back(comp);
						program.number_of_complitions++;
					}
				}			// if THERE ARE MORE THAN ONE RULE
				else {
					comp->connector = OR;
					comp->head = curAtom;
					for (list<NestedRule*>::iterator itrNRule =
							curAtom->nestedRules.begin();
							itrNRule != curAtom->nestedRules.end();
							++itrNRule) {
						cr = (*itrNRule);
						markNestedRule(cr);
						createNestedRuleBodyAClause(cr);
						//creates an auxilary atom that corresponds to body && head(minus cur atom)
						//also adds the equality for that atom
						//if basic rule
						if (cr->sizeHead() == 1) {
							if (cr->signReprComp == POS)
								api->add_Cbody(cr->reprComp, true);
							else if (cr->signReprComp == NEG)
								api->add_Cbody(cr->reprComp, false);
							else {
								cout << "Error the reprComp is not defined";
								exit(0);
							}
						} else {//if disj rule we have to add negation to the clause
							//THIS AUX ATOM IS CREATED TWICE!
							if (cr->end - cr->head == 2) {//if the rule is of the form h1 v h2.
								if (comp->head == cr->head[0]) {
									api->add_Cbody(cr->head[1], false);
								} else
									api->add_Cbody(cr->head[0], false);
							}
							Atom* aux = createAuxAtom(comp->head, cr);
							if (!aux)
								cout << "Error: Aux atom is null";
							else
								api->add_Cbody(aux, true);
						}
					}
					comp->initCompletionNbodyFromCompApi(api);
					resetCompApi();
					program.completions.push_back(comp);
					program.number_of_complitions++;

				}
			}
		}
	}
	return;
}
inline void Cmodels::markNestedRule(NestedRule* cr) {
	//the rule is the fact
	//no representative is needed

	if (cr->nbody == cr->nnend && cr->sizeHead() == 1) { //basic rule and is the fact
		api->set_compute(cr->head[0], true, true);
		return;
	}
	if (cr->nbody == cr->nnend) //disj rule
		return;
	if (cr->reprComp != 0)
		return;
	// only one positive or bouble negated atom in the rule
	if (cr->sizeBody() == 1 && cr->nbody == cr->nend) {
		cr->signReprComp = POS;
		cr->reprComp = cr->pbody[0];
		return;
	} else if (cr->sizeBody() == 1) {
		cr->signReprComp = NEG;
		cr->reprComp = cr->nbody[0];
		return;
	}
	createRepresentative(cr);
}

void Cmodels::createRankingFormula() {
	//get the number of atoms in order to declare cspvar(x,0,NumOfAtom)
	long curAtomsSize = program.atoms.size();
	long cmSize = program.completions.size();

	for (long indA = 0; indA < curAtomsSize; indA++) {
		Atom *curAtom = program.atoms[indA];
		if (!curAtom->name)
			break;
		if (strcmp(curAtom->name, "cspdomain(r)") == 0) {
			api->set_name(curAtom, "cspdomain(mixed)");
			break;
		} else if (strcmp(curAtom->name, "cspdomain(fd)") == 0) {
			break;
		}
	}

	std::ostringstream ss;
	ss.clear();
	ss.str("");
	ss << program.number_of_atoms;
	string NumOfAtom = ss.str();

	for (long indA = 0; indA < curAtomsSize; indA++) {
		Atom *curAtom = program.atoms[indA];
		NestedRule* cr;
		//we do nothing for atoms that are not in heads of rules
		if (curAtom->nestedRules.size() == 0) {
			// cout<<"not in head"<<endl;
		} else {
			//we add constraint for condition 1.
			Completion *comp = new Completion();
			comp->eq = IMPL;
			comp->connector = OR;
			comp->head = curAtom;
			for (list<NestedRule*>::iterator itrNRule =
					curAtom->nestedRules.begin();
					itrNRule != curAtom->nestedRules.end(); ++itrNRule) {
				cr = (*itrNRule);
				//if B+ is not empty
				if (cr->pbody != cr->pend) {
					//we check whether there is an atom a in B+ such that a is a head of a rule.
					bool empty_set = true;
					for (Atom **bodyAtom = cr->pbody; bodyAtom != cr->pend;
							bodyAtom++) {
						if ((*bodyAtom)->nestedRules.size() > 0)
							empty_set = false;
					}
					if (!empty_set) {
						//There is an atom a in B+ such that a is a head of a rule.
						//creates an auxilary atom that corresponds to conjunction of body and level ranking variable
						if (!cr->reprComp2)
							cr->reprComp2 = createAuxAtom2(curAtom, cr);
						api->add_Cbody(cr->reprComp2, true);
					} else {
						//there is no atom a in B+ such that a is a head of a rule.
						if (!cr->signReprComp)
							createRepresentative(cr);
						if (cr->signReprComp == POS)
							api->add_Cbody(cr->reprComp, true);
						else if (cr->signReprComp == NEG)
							api->add_Cbody(cr->reprComp, false);
						else {
							cout << "Error the reprComp is not defined" << endl;
							cr->print();
							exit(0);
						}
					}
				} else {
					if (!cr->signReprComp)
						createRepresentative(cr);
					if (cr->signReprComp == POS)
						api->add_Cbody(cr->reprComp, true);
					else if (cr->signReprComp == NEG)
						api->add_Cbody(cr->reprComp, false);
					else {
						cout << "Error the reprComp is not defined" << endl;
						cr->print();
						exit(0);
					}
				}						//curAtom->nestedRules.size()
			}
			comp->initCompletionNbodyFromCompApi(api);
			resetCompApi();
			if (comp->pbody != comp->pend) {
				if (param.rdcComp != true) {
					program.completions.push_back(comp);
					program.number_of_complitions++;
				} else {
					//Now we remove the completion whose head is curAtom
					//before pushing the level ranking formula into the vector of completion
					int count = 0;
					for (long indCm = 0; indCm < cmSize; indCm++) {
						Completion* comp2 = program.completions[indCm];
						if ((comp2->head)->id == curAtom->id) {
							program.completions[indCm] = comp;
							count++;
						}
					}
					if (count == 0) {
						program.completions.push_back(comp);
						program.number_of_complitions++;
						cout << "Warning: completion is not created for atom ";
						curAtom->print();
						cout << endl;
					} else if (count > 1) {
						cerr
								<< "Error: completion is created repeatedly for atom ";
						curAtom->print();
						cerr << endl;
					}
				}

			} else {
				cout << "empty completion" << endl;
				exit(0);
			}
		}
	}

	//add constraint for condition 2 and 3
	if (param.sys == LEVEL_RANKING_STRONG)
		createStrongRankingFormula(curAtomsSize, NumOfAtom);

	// add cspvar(lr)  in out put
	for (int i = 0; i < LRVarIDs.size(); i++) {
		if (LRVarIDs[i] == 1) {
			ss.clear();
			ss.str("");
			ss << i;
			string varName("cspvar(lr");
			varName += ss.str();
			varName += ",1,";
			varName += NumOfAtom;
			varName += ")";

			Atom *LRVar = api->new_atom();
			api->set_name(LRVar, varName.c_str());
			resetApi();
			api->add_body(LRVar, true);
			Clause *cl = new Clause();
			cl->initClauseFromApi(api);
			resetApi();
			program.number_of_clauses++;
			program.clauses.push_back(cl);
			cl->finishClause();

		}
	}
	return;
}

void Cmodels::createSCCRankingFormula() {
	vector<list<Atom*>*>* NTSCCs = new vector<list<Atom*>*>; //the list contains non-trivial SCCs
	long curAtomsSize = program.atoms.size();
	long cmSize = program.completions.size();

	for (long indA = 0; indA < curAtomsSize; indA++) {
		Atom *curAtom = program.atoms[indA];
		if (!curAtom->name)
			break;
		if (strcmp(curAtom->name, "cspdomain(r)") == 0) {
			api->set_name(curAtom, "cspdomain(mixed)");
			break;
		} else if (strcmp(curAtom->name, "cspdomain(fd)") == 0) {
			break;
		}
	}

	//read in non-trivial SCCs from inLoop and store them in NTSCCs
	int maxloop = -1;
	for (long indA = 0; indA < curAtomsSize; indA++) {
		if (program.atoms[indA]->inLoop > maxloop)
			maxloop = program.atoms[indA]->inLoop;
	}
	if (maxloop >= 0)
		NTSCCs->resize(maxloop + 1);
	else {
		cout << "error, the program is tight." << endl;
		return;
	}

	for (long indA = 0; indA < curAtomsSize; indA++) {
		Atom *curAtom = program.atoms[indA];
		if (curAtom->inLoop != -1) {
			if (!(*NTSCCs)[curAtom->inLoop]) {
				(*NTSCCs)[curAtom->inLoop] = new list<Atom*>;
			}
			(*NTSCCs)[curAtom->inLoop]->push_back(curAtom);
		}
	}

	//get the number of atoms in order to declare cspvar(x,0,NumOfAtom)
	std::ostringstream ss;
	ss.clear();
	ss.str("");
	ss << program.number_of_atoms;
	string NumOfAtom = ss.str();

	//get the number in a SCC in order to declare cspvar(x,0,NumofSCCAtoms[Loop])
	vector<int> NumofSCCAtoms;
	NumofSCCAtoms.clear();
	NumofSCCAtoms.resize(maxloop + 1);
	for (long indA = 0; indA < curAtomsSize; indA++) {
		Atom *curAtom = program.atoms[indA];
		if (curAtom->inLoop != -1) {
			NumofSCCAtoms[curAtom->inLoop]++;
		}
	}
	/*
	 for(int i =0; i<NumofSCCAtoms.size();i++){
	 cout<<i<<" "<<NumofSCCAtoms[i]<<endl;
	 }*/

	//iterate through NTSCCs to add ranking formula
	Atom *curAtom;
	for (int SCCid = 0; SCCid < NTSCCs->size(); SCCid++) {
		for (list<Atom*>::iterator itrAtom = (*NTSCCs)[SCCid]->begin();
				itrAtom != (*NTSCCs)[SCCid]->end(); ++itrAtom) {
			curAtom = *itrAtom;
			list<NestedRule*>* ext = new list<NestedRule*>; //the list to store non-Recursive rules to be used in external support

			NestedRule* cr;
			//go through the rules whose head is curAtom.
			for (list<NestedRule*>::iterator itrNRule =
					curAtom->nestedRules.begin();
					itrNRule != curAtom->nestedRules.end(); ++itrNRule) {
				cr = (*itrNRule);
				//creates an auxilary atom that corresponds to conjunction of body and level ranking variable,
				//and mark recursive rules
				createAuxAtomSCC(cr, (*NTSCCs)[SCCid]);
			}
			Completion *comp = new Completion();
			comp->eq = IMPL;
			comp->connector = OR;
			comp->head = curAtom;
			for (list<NestedRule*>::iterator itrNRule =
					curAtom->nestedRules.begin();
					itrNRule != curAtom->nestedRules.end(); ++itrNRule) {
				cr = (*itrNRule);
				//if non-recursive rule, add reprComp(body auxilary) into the external support list.
				if (!cr->isRR) {
					ext->push_back(cr);
				} else {
					//if recursive rule, add ranking variable
					api->add_Cbody(cr->reprComp2, true);
				}
			}
			Atom *exta = api->new_atom();
			exta->headof++;
			api->add_Cbody(exta, true);
			comp->initCompletionNbodyFromCompApi(api);
			resetCompApi();
			if (comp->pbody != comp->pend) {
				if (param.rdcComp != true) {
					program.completions.push_back(comp);
					program.number_of_complitions++;
				} else {
					//Now we remove the completion whose head is curAtom
					//before pushing the level ranking formula into the vector of completion
					int count = 0;
					for (long indCm = 0; indCm < cmSize; indCm++) {
						Completion* comp2 = program.completions[indCm];
						if ((comp2->head)->id == curAtom->id) {
							program.completions[indCm] = comp;
							count++;
						}
					}
					if (count == 0) {
						program.completions.push_back(comp);
						program.number_of_complitions++;
						cout << "Warning: completion is not created for atom ";
						curAtom->print();
						cout << endl;
					} else if (count > 1) {
						cerr
								<< "Error: completion is created repeatedly for atom ";
						curAtom->print();
						cerr << endl;
					}
				}
			}

			//add clauses for exta
			for (list<NestedRule*>::iterator itrNRule = ext->begin();
					itrNRule != ext->end(); ++itrNRule) {
			}
			if (ext->empty()) {
				Clause *cl = new Clause();
				api->add_body(exta, false);
				cl->initClauseFromApi(api);
				resetApi();
				program.number_of_clauses++;
				program.clauses.push_back(cl);
				cl->finishClause();
			} else {
				//Firstly, add exta -> body1 or body2 or body3...
				Clause *cl1 = new Clause();
				api->add_body(exta, false);
				for (list<NestedRule*>::iterator itrNRule = ext->begin();
						itrNRule != ext->end(); ++itrNRule) {
					if ((*itrNRule)->signReprComp == POS)
						api->add_body((*itrNRule)->reprComp, true);
					else if ((*itrNRule)->signReprComp == NEG)
						api->add_body((*itrNRule)->reprComp, false);
					else {
						createRepresentative((*itrNRule));
						if ((*itrNRule)->signReprComp == POS)
							api->add_body((*itrNRule)->reprComp, true);
						else if ((*itrNRule)->signReprComp == NEG)
							api->add_body((*itrNRule)->reprComp, false);
						else
							cout << "error: reprComp is not defined" << endl;
					}
				}
				cl1->initClauseFromApi(api);
				resetApi();
				program.number_of_clauses++;
				program.clauses.push_back(cl1);
				cl1->finishClause();

				//then add body -> exta
				for (list<NestedRule*>::iterator itrNRule = ext->begin();
						itrNRule != ext->end(); ++itrNRule) {
					Clause *cl2 = new Clause();
					api->add_body(exta, true);
					if ((*itrNRule)->signReprComp == POS)
						api->add_body((*itrNRule)->reprComp, false);
					else if ((*itrNRule)->signReprComp == NEG)
						api->add_body((*itrNRule)->reprComp, true);
					else {
						createRepresentative((*itrNRule));
						if ((*itrNRule)->signReprComp == POS)
							api->add_body((*itrNRule)->reprComp, false);
						else if ((*itrNRule)->signReprComp == NEG)
							api->add_body((*itrNRule)->reprComp, true);
						else
							cout << "error: reprComp is not defined" << endl;
					}
					cl2->initClauseFromApi(api);
					resetApi();
					program.number_of_clauses++;
					program.clauses.push_back(cl2);
					cl2->finishClause();
				}
			}

			if (param.sys == SCC_LEVEL_RANKING_STRONG) {
				//add clause for strong ranking condition 2: exta-> lr(a)=1
				Clause *cl = new Clause();
				api->add_body(exta, false);
				Atom *rankingVar = api->new_atom();
				ss.clear();
				ss.str("");
				string varName("required(ezcsp__eq(lr");
				ss << curAtom->id;
				varName += ss.str();
				varName += ",1))";
				api->set_name(rankingVar, varName.c_str());
				api->add_body(rankingVar, true);

				// add IDs of Level Ranking Variables to LRVarIDs, in order to add cspvar(lr) in output.
				if (curAtom->id >= LRVarIDs.size())
					LRVarIDs.resize(curAtom->id + 1);
				if (curAtom->inLoop == 0)
					LRVarIDs[curAtom->id] = -2;
				else
					LRVarIDs[curAtom->id] = curAtom->inLoop;

				cl->initClauseFromApi(api);
				resetApi();
				program.number_of_clauses++;
				program.clauses.push_back(cl);
				cl->finishClause();
			}

		}
	}

	if (param.sys == SCC_LEVEL_RANKING_STRONG)
		createStrongSCCRankingFormulaCondition3(NTSCCs);

	// add cspvar(lr)  in out put
	for (int i = 0; i < LRVarIDs.size(); i++) {
		if (LRVarIDs[i] != -1 && LRVarIDs[i] != 0) {
			ss.clear();
			ss.str("");
			ss << i;
			string varName("cspvar(lr");
			varName += ss.str();
			varName += ",1,";

			if (param.mnmBd == true) {//smaller upper bound as the number of atoms in this SCC
				ss.clear();
				ss.str("");
				if (LRVarIDs[i] == -2)	//we use -2 to represent inLoop == 0.
					ss << NumofSCCAtoms[0];
				else if (NumofSCCAtoms[LRVarIDs[i]] == -1
						|| NumofSCCAtoms[LRVarIDs[i]] == 0
						|| NumofSCCAtoms[LRVarIDs[i]] == 1)
					cout << "Error: Atom " << i << " is Not in NTSCCs." << endl;
				else
					ss << NumofSCCAtoms[LRVarIDs[i]];
				varName += ss.str();
			} else
				varName += NumOfAtom; //maximal upper bound

			varName += ")";

			Atom *LRVar = api->new_atom();
			api->set_name(LRVar, varName.c_str());
			resetApi();
			api->add_body(LRVar, true);
			Clause *cl = new Clause();
			cl->initClauseFromApi(api);
			resetApi();
			program.number_of_clauses++;
			program.clauses.push_back(cl);
			cl->finishClause();
		}
	}

	return;
}

void Cmodels::createRepresentative(NestedRule* cr) {

	Atom *newa = api->new_atom();
	newa->headof++;
	/*  cout<<" ATOM ";
	 newa->print();
	 cr->print();
	 */
	cr->reprComp = newa;
	cr->signReprComp = POS;

	Completion *comp1 = new Completion();
	comp1->head = newa;
	comp1->connector = AND;

	placeToApi(cr->nbody, cr->nend, false);
	placeToApi(cr->pbody, cr->nnend, true);

	comp1->initCompletionNbodyFromApi(api);

	resetApi();

	program.completions.push_back(comp1);
	program.number_of_complitions++;
}

Atom * Cmodels::createAuxAtom(Atom * head, NestedRule * cr) {
	Atom *newa = api->new_atom();
	newa->headof++;
	Completion *comp1 = new Completion();
	comp1->head = newa;
	comp1->connector = AND;
	//and additional comp1 for auxilary atom

	for (Atom **a = cr->head; a != cr->hend; a++) {
		if ((*a)->id != head->id)
			api->add_body((*a), false);
	}
	if (cr->reprComp && cr->signReprComp == POS)
		api->add_body(cr->reprComp, true);
	else if (cr->reprComp && cr->signReprComp == NEG)
		api->add_body(cr->reprComp, false);
	else
		assert(cr->nbody == cr->end); //rule has empty body
	//	cout<<"Error: repr atom is null";
	comp1->initCompletionNbodyFromApi(api);
	resetApi();
	program.completions.push_back(comp1);
	program.number_of_complitions++;
	return newa;
}

Atom * Cmodels::createAuxAtom2(Atom * head, NestedRule * cr) {
	Atom *newa = api->new_atom();
	newa->headof++;
	Completion *comp1 = new Completion();
	comp1->head = newa;
	comp1->connector = AND;
	//if reprComp does not exist, create reprComp.
	//if reprComp exists, add reprComp to api to represent Body.
	if (cr->signReprComp == POS)
		api->add_body(cr->reprComp, true);
	else if (cr->signReprComp == NEG)
		api->add_body(cr->reprComp, false);
	else {
		createRepresentative(cr);
		if (cr->signReprComp == POS)
			api->add_body(cr->reprComp, true);
		else if (cr->signReprComp == NEG)
			api->add_body(cr->reprComp, false);
		else
			cout << "error: reprComp is not defined" << endl;
	}
	//add level ranking variables.
	std::ostringstream idStream;
	for (Atom ** b = cr->pbody; b != cr->pend; b++) {
		//we do nothing for b that is not in heads of rules
		if ((*b)->nestedRules.begin() == (*b)->nestedRules.end()) {
			//	cout<<"atom not in head"<<endl;
		} else {
			//if b is in heads of rules, we add level ranking variable
			idStream.clear();
			Atom *rankingVar = api->new_atom();
			string varName("required(ezcsp__geq(ezcsp__pl(lr");
			idStream.str("");
			idStream << (*cr->head)->id;
			varName += idStream.str();
			varName += ",-1),lr";
			idStream.str("");
			idStream << (*b)->id;
			varName += idStream.str();
			varName += "))";
			api->set_name(rankingVar, varName.c_str());
			api->add_body(rankingVar, true);

			//mark the IDs of Level Ranking Variables in LRVarIDs, in order to add cspvar(lr) in output.
			if ((*cr->head)->id > (*b)->id
					&& (*cr->head)->id >= LRVarIDs.size())
				LRVarIDs.resize((*cr->head)->id + 1);
			if ((*cr->head)->id <= (*b)->id && (*b)->id >= LRVarIDs.size())
				LRVarIDs.resize((*b)->id + 1);
			LRVarIDs[(*cr->head)->id] = 1;
			LRVarIDs[(*b)->id] = 1;
		}
	}
	comp1->initCompletionNbodyFromApi(api);
	resetApi();
	if (comp1->pbody != comp1->pend) {
		program.completions.push_back(comp1);
		program.number_of_complitions++;
	} else {
		cout << "empty completion" << endl;
		exit(0);
	}
	return newa;
}

void Cmodels::createAuxAtomSCC(NestedRule* cr, list<Atom*>* SCC) {
	//Create auxiliary atom for conjunctions in level ranking formula. And set isRR.
	bool recursive = false;
	//go through bodies, if recursive, set recursive and add level ranking variables to api.
	std::ostringstream idStream;
	for (Atom ** b = cr->pbody; b != cr->pend; b++) {
		bool intersect = false;
		for (list<Atom*>::iterator itrAtom = SCC->begin();
				itrAtom != SCC->end(); ++itrAtom) {
			if ((*itrAtom)->id == (*b)->id) {
				intersect = true;
				break;
			}
		}
		if (intersect) {
			recursive = true;
			idStream.clear();
			Atom *rankingVar = api->new_atom();
			string varName("required(ezcsp__geq(ezcsp__pl(lr");
			idStream.str("");
			idStream << (*cr->head)->id;
			varName += idStream.str();
			varName += ",-1),lr";
			idStream.str("");
			idStream << (*b)->id;
			varName += idStream.str();
			varName += "))";
			api->set_name(rankingVar, varName.c_str());
			api->add_Cbody(rankingVar, true);

			//mark the IDs of Level Ranking Variables in LRVarIDs, in order to add cspvar(lr) in output.
			if ((*cr->head)->id > (*b)->id
					&& (*cr->head)->id >= LRVarIDs.size())
				LRVarIDs.resize((*cr->head)->id + 1);
			if ((*cr->head)->id <= (*b)->id && (*b)->id >= LRVarIDs.size())
				LRVarIDs.resize((*b)->id + 1);
			if ((*cr->head)->inLoop == 0)
				LRVarIDs[(*cr->head)->id] = -2;
			else
				LRVarIDs[(*cr->head)->id] = (*cr->head)->inLoop;
			if ((*b)->inLoop == 0)
				LRVarIDs[(*b)->id] = -2;
			else
				LRVarIDs[(*b)->id] = (*b)->inLoop;
		}
	}
	if (recursive) {
		Atom *newa = api->new_atom();
		newa->headof++;
		Completion *comp1 = new Completion();
		comp1->head = newa;
		comp1->connector = AND;
		//if reprComp does not exist, create reprComp.
		//if reprComp exists, add reprComp to api to represent Body.
		if (cr->signReprComp == POS)
			api->add_Cbody(cr->reprComp, true);
		else if (cr->signReprComp == NEG)
			api->add_Cbody(cr->reprComp, false);
		else {
			createRepresentative(cr);
			if (cr->signReprComp == POS)
				api->add_Cbody(cr->reprComp, true);
			else if (cr->signReprComp == NEG)
				api->add_Cbody(cr->reprComp, false);
			else
				cout << "error: reprComp is not defined" << endl;
		}
		comp1->initCompletionNbodyFromCompApi(api);
		resetCompApi();
		program.completions.push_back(comp1);
		program.number_of_complitions++;
		cr->reprComp2 = newa;
		cr->isRR = true;
	} else {
		cr->isRR = false;
		resetCompApi();
	}
}

Atom * Cmodels::createAuxAtomHeadBody(Atom * head, NestedRule * cr) {
	//Create auxiliary atom for (a and body) in the head of completion in strong level ranking formula condition 3.
	Atom *newa = api->new_atom();
	newa->headof++;
	Completion *comp1 = new Completion();
	comp1->head = newa;
	comp1->connector = AND;

	api->add_Cbody(head, true);
	//if reprComp does not exist, add atoms in body to api.
	//if reprComp exists, add reprComp to api to represent Body.
	if (cr->signReprComp == POS)
		api->add_Cbody(cr->reprComp, true);
	else if (cr->signReprComp == NEG)
		api->add_Cbody(cr->reprComp, false);
	else {
		createRepresentative(cr);
		if (cr->signReprComp == POS)
			api->add_Cbody(cr->reprComp, true);
		else if (cr->signReprComp == NEG)
			api->add_Cbody(cr->reprComp, false);
		else
			cout << "error: reprComp is not defined" << endl;
	}
	comp1->initCompletionNbodyFromCompApi(api);
	resetCompApi();
	program.completions.push_back(comp1);
	program.number_of_complitions++;
	return newa;
}

void Cmodels::createStrongRankingFormula(long curAtomsSize, string NumOfAtom) {
	//create constraints for strong level ranking condition 2 and 3.
	std::ostringstream idStream;
	idStream.clear();
	idStream.str("");
	for (long indA = 0; indA < curAtomsSize; indA++) {
		Atom *curAtom = program.atoms[indA];
		//we do nothing for rules which are not in heads of rules
		if (curAtom->nestedRules.begin() == curAtom->nestedRules.end()) {
			//cout<<"not in head"<<endl;
		} else {
			for (list<NestedRule*>::iterator itrNRule =
					curAtom->nestedRules.begin();
					itrNRule != curAtom->nestedRules.end(); ++itrNRule) {
				NestedRule* cr = (*itrNRule);
				//create completion
				Completion *comp = new Completion();
				comp->eq = IMPL;
				comp->connector = OR;
				comp->head = createAuxAtomHeadBody(curAtom, cr);//create an auxiliary atom that corresponds to the a^Body

				//we add constraint for condition 3 when B+ is not empty.
				if (cr->pbody != cr->pend) {
					//add strong level ranking variables.
					for (Atom ** b = cr->pbody; b != cr->pend; b++) {
						idStream.clear();
						Atom *rankingVar = api->new_atom();
						string varName("required(ezcsp__geq(ezcsp__pl(lr");
						idStream.str("");
						idStream << (*b)->id;
						varName += idStream.str();
						varName += ",1),lr";
						idStream.str("");
						idStream << (*cr->head)->id;
						varName += idStream.str();
						varName += "))";
						api->set_name(rankingVar, varName.c_str());
						api->add_Cbody(rankingVar, true);

						//mark the IDs of Level Ranking Variables in LRVarIDs, in order to add cspvar(lr) in output.
						if ((*cr->head)->id > (*b)->id
								&& (*cr->head)->id >= LRVarIDs.size())
							LRVarIDs.resize((*cr->head)->id + 1);
						if ((*cr->head)->id <= (*b)->id
								&& (*b)->id >= LRVarIDs.size())
							LRVarIDs.resize((*b)->id + 1);
						LRVarIDs[(*cr->head)->id] = 1;
						LRVarIDs[(*b)->id] = 1;
					}
				} else {
					//we add constraint for condition 2 when B+ is  empty.
					Atom *rankingVar = api->new_atom();
					idStream.clear();
					idStream.str("");
					string varName("required(ezcsp__eq(lr");
					idStream << curAtom->id;
					varName += idStream.str();
					varName += ",1))";
					api->set_name(rankingVar, varName.c_str());
					api->add_Cbody(rankingVar, true);
					//mark the IDs of Level Ranking Variables in LRVarIDs, in order to add cspvar(lr) in output.
					if (curAtom->id >= LRVarIDs.size())
						LRVarIDs.resize(curAtom->id + 1);
					LRVarIDs[curAtom->id] = 1;
				}
				comp->initCompletionNbodyFromCompApi(api);
				resetCompApi();
				if (comp->pbody != comp->pend) {
					program.completions.push_back(comp);
					program.number_of_complitions++;
				} else {
					cout << "Empty Completion" << endl;
					exit(0);
				}
			}
		}

	}
	return;
}

void Cmodels::createStrongSCCRankingFormulaCondition3(
		vector<list<Atom*>*>* NTSCCs) {
	Atom *curAtom;
	std::ostringstream idStream;
	idStream.clear();
	idStream.str("");
	//iterate throught NTSCCs
	for (int SCCid = 0; SCCid < NTSCCs->size(); SCCid++) {
		for (list<Atom*>::iterator itrAtom = (*NTSCCs)[SCCid]->begin();
				itrAtom != (*NTSCCs)[SCCid]->end(); ++itrAtom) {
			curAtom = *itrAtom;
			NestedRule* cr;
			for (list<NestedRule*>::iterator itrNRule =
					curAtom->nestedRules.begin();
					itrNRule != curAtom->nestedRules.end(); ++itrNRule) {
				cr = (*itrNRule);
				//if cr is a recursive rule
				if (cr->isRR) {
					Completion *comp = new Completion();
					comp->eq = IMPL;
					comp->connector = OR;
					comp->head = createAuxAtomHeadBody(curAtom, cr);
					//add strong level ranking variables.
					for (Atom ** b = cr->pbody; b != cr->pend; b++) {
						//initiate a boolean intersect which indicates that b is in the intersection of B+ and SCC(a)
						bool intersect = false;
						for (list<Atom*>::iterator itrAtom =
								(*NTSCCs)[SCCid]->begin();
								itrAtom != (*NTSCCs)[SCCid]->end(); ++itrAtom) {
							if ((*itrAtom)->id == (*b)->id) {
								intersect = true;
								break;
							}
						}
						if (intersect) {
							idStream.clear();
							Atom *rankingVar = api->new_atom();
							string varName("required(ezcsp__geq(ezcsp__pl(lr");
							idStream.str("");
							idStream << (*b)->id;
							varName += idStream.str();
							varName += ",1),lr";
							idStream.str("");
							idStream << (*cr->head)->id;
							varName += idStream.str();
							varName += "))";
							api->set_name(rankingVar, varName.c_str());
							api->add_Cbody(rankingVar, true);

							//mark the IDs of Level Ranking Variables in LRVarIDs, in order to add cspvar(lr) in output.
							if ((*cr->head)->id > (*b)->id
									&& (*cr->head)->id >= LRVarIDs.size())
								LRVarIDs.resize((*cr->head)->id + 1);
							if ((*cr->head)->id <= (*b)->id
									&& (*b)->id >= LRVarIDs.size())
								LRVarIDs.resize((*b)->id + 1);
							if ((*cr->head)->inLoop == 0)
								LRVarIDs[(*cr->head)->id] = -2;
							else
								LRVarIDs[(*cr->head)->id] = (*cr->head)->inLoop;
							if ((*b)->inLoop == 0)
								LRVarIDs[(*b)->id] = -2;
							else
								LRVarIDs[(*b)->id] = (*b)->inLoop;

						}
					}
					comp->initCompletionNbodyFromCompApi(api);
					resetCompApi();
					assert(comp->pbody != comp->pend);
					program.completions.push_back(comp);
					program.number_of_complitions++;
				}
			}
		}
	}
	return;
}

void Cmodels::createFalseHeadClauses(Atom* acl) {

	NestedRule* cr;
	for (list<NestedRule*>::iterator itrNRule = acl->nestedRules.begin();
			itrNRule != acl->nestedRules.end(); ++itrNRule) {
		cr = (*itrNRule);
		assert(cr->sizeHead() == 1);	//only basic rules can come here

		//the corresponding clause will be : -b1 v ...v-bn
		//hence we read everything reverse
		//we create the clause as for basic rule
		placeToApi(cr->nbody, cr->nend, true);
		placeToApi(cr->pbody, cr->nnend, false);

		Clause *cl = new Clause();			//will be : -b1 v ...v-bn  ->
		cl->initClauseFromApi(api);
		program.number_of_clauses++;
		program.clauses.push_back(cl);
		cl->finishClause();
		resetApi();
		delete cr;
	}
	acl->nestedRules.clear();

}

void Cmodels::placeToApi(Atom** start, Atom** end, bool truth) {
	for (Atom **a = start; a != end; a++)
		api->add_body((*a), truth);
}
inline void Cmodels::resetApi() {
	api->rule_reset();
}

//Creates Body imlies Head clause
inline void Cmodels::createNestedRuleBodyAClause(NestedRule *rb) {
	//if Body->A clause still does not exist

	if (!rb->bodyACl) {
		rb->bodyACl = true;

		placeToApi(rb->head, rb->hend, true);
		if (rb->reprComp == 0) {
			placeToApi(rb->nbody, rb->nend, true);
			placeToApi(rb->pbody, rb->nnend, false);
		} else {
			if (rb->signReprComp == POS)
				api->add_body(rb->reprComp, false);
			else
				api->add_body(rb->reprComp, true);
		}
		Clause *cl = new Clause();	//will be : -b1 v ...v-bn  v h1 v...v hn
		cl->initClauseFromApi(api);
		program.number_of_clauses++;
		program.clauses.push_back(cl);
		cl->finishClause();

		resetApi();

	}
}

Result Cmodels::createClauses() {

	//now we go thru all completion heads

	resetApi();

	Completion* comp;
	Clause * cl;
	long cmSize = program.completions.size();
	for (long indCm = 0; indCm < cmSize; indCm++) {
		comp = program.completions[indCm];
		//case 2: Head = T means that nbody of completion is empty
		if (!comp->nbody) {
			api->set_compute(comp->head, true, true);
		}	//if body is not empty
		else {
			resetApi();
			placeToApi(comp->nbody, comp->nend, false);
			placeToApi(comp->pbody, comp->pend, true);

			if (api->sizeBody() == 1 && api->sizeNbody() == 1
					&& comp->nbody[0] == comp->head) {//in case when completion is of the form:
					// p<->-p
					//we reach the conflict and return false
					//	cout<<"WE are at p=-p";
				return UNSAT;

			}

			if (api->sizeBody() == 1 && api->sizePbody() == 1
					&& comp->nbody[0] == comp->head) {//in case when p<->p v p->p
				createDoubleClause(comp->head, comp->head, true, false);
			} else {
				switch (comp->connector) {
				case OR:		//case 1: Head:- b1 v b2 ..bn
					//-head v b1 v ...vbn
					// -b1 v head, .. -bn v head
					assert(comp->eq == IMPL);
					//case 1.5 - enought to do it one direction atom=>Body or T=>Body

					cl = new Clause();	      //will be  -head v b1 v ...vbn
					int num;
					if (comp->head->Bpos)
						cl->allocateClause(api->sizeNbody(), api->sizePbody());
					else
						cl->allocateClause(1 + api->sizeNbody(),
								api->sizePbody());
					int i;
					for (i = 0; i < api->sizeNbody(); i++) {
						cl->addNbody(i, api->nbodyAtom(i));
					}
					if (!comp->head->Bpos) {
						cl->addNbody(i, comp->head);
					}

					for (i = 0; i < api->sizePbody(); i++) {
						cl->addPbody(i, api->pbodyAtom(i));
					}
					program.number_of_clauses++;
					program.clauses.push_back(cl);
					cl->finishClause();

					break;
				case AND:
					// case 2: when COMPLETION h<->b1 & b2 &...& bn
					//h v -b1 v ...v-bn
					// b1 v -h, .. bn v -h
					switch (comp->eq) {
					case EQUIV:
						assert(!comp->head->Bpos); //the only time when we have equive connector
						// is with auxilary atoms
						// hence we are not aware if they are Pos or Neg
						cl = new Clause();       //will be h v -b1 v ...v-bn
						cl->allocateClause(api->sizePbody(),
								api->sizeNbody() + 1);
						for (i = 0; i < api->sizePbody(); i++) {
							cl->addNbody(i, api->pbodyAtom(i));
							//-h v bi
							createDoubleClause(comp->head, api->pbodyAtom(i),
									false, true);

						}
						cl->addPbody(0, comp->head); //head is positive atom and negative atoms turn to positive
						//since double negation
						for (i = 0; i < api->sizeNbody(); i++) {
							cl->addPbody(i + 1, api->nbodyAtom(i));

							//-h v -bi in this case since this is negative bi's
							createDoubleClause(comp->head, api->nbodyAtom(i),
									false, false);
						}

						program.number_of_clauses++;
						program.clauses.push_back(cl);
						cl->finishClause();

						break;
					case IMPL:
						//we do it only in one
						//direction a impl Body when it is

						int i;
						for (i = 0; i < api->sizePbody(); i++) {
							//-h v bi
							createDoubleClause(comp->head, api->pbodyAtom(i),
									false, true);
						}
						//since double negation
						for (i = 0; i < api->sizeNbody(); i++) {
							//-h v -bi in this case since this is negative bi's
							createDoubleClause(comp->head, api->nbodyAtom(i),
									false, false);
						}
						break;
					}

				}
			}

		}

		//
		// we delete a completion as at the moment we created
		// nested rule and added it to another list
		delete comp;

	}
	program.completions.clear();
	return (Result) UNKNOWN;
}

void Cmodels::createSingleAtomClauses() {
	// case 4: Head = F means that pbody of completion is empty
	// and may happen when atom is never in the head
	//+
	//if atom is in positive part of compute{} we will add it as a clause
	//if it is in a neg part of compute{}
	//we will add him as -it

	for (long indA = 0; indA < program.atoms.size(); indA++) {
		Atom* atom = program.atoms[indA];
		if (atom->headof == 0) {
			api->set_compute(atom, false);
		}
		if (atom->Bpos) {
			api->set_compute(atom, true, true);
		}
		if (atom->Bneg) {
			add_clause_from_compute(atom, false);
		}
		if (atom->computeTrue || atom->computeTrue0) {
			add_clause_from_compute(atom, true);
		}
	}
	resetApi();
	return;

}

inline void Cmodels::add_clause_from_compute(Atom *a, bool pos) {

	assert(a);
	Clause *cl = new Clause();

	if (pos) {
		cl->allocateClause(0, 1);
	} else {
		cl->allocateClause(1, 0);
	}
	cl->addBody(0, a);
	program.number_of_clauses++;
	cl->finishClause();
	program.clauses.push_back(cl);

}

inline void Cmodels::print_completion() {
	program.print_completion();
}

inline void Cmodels::print_clauses() {
	program.print_clauses();
}


void Cmodels::writeToSmtLibFile(string outputFileName)
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
	if (param.sys == CASP_DIMACS_PRODUCE || param.sys == DIMACS_PRODUCE
			|| param.sys == SCC_LEVEL_RANKING || param.sys == LEVEL_RANKING
			|| param.sys == SCC_LEVEL_RANKING_STRONG
			|| param.sys == LEVEL_RANKING_STRONG
			|| (program.tight
					&& (param.sys == RELSAT || param.sys == ASSAT_ZCHAFF))
			|| param.sys == SIMO) {
		for (long indA = 0; indA < program.clauses.size(); indA++) {
			delete program.clauses[indA];
		}
		program.clauses.clear();
	}
}

//At this point  rulesOfLoopsHeads[inLoop] must contain
//all the rules neseccery to build loop formula

void Cmodels::loopRulesInit(const int& numSCC, vector<Atom*>* atomsSCC,
		vector<NestedRule*>* rulesOfLoopsHeads) {

	for (int indAinLoop = 0; indAinLoop < numSCC; indAinLoop++) {
		loopRulesInitSCC(atomsSCC[indAinLoop], rulesOfLoopsHeads[indAinLoop]);
	}
	return;
}
void Cmodels::loopRulesInitSCC(vector<Atom*> &atomsSCC,
		vector<NestedRule*> &rulesOfLoopsHeads) {

	//we can add nec. the one R^-(L)rules as follows
	//if(conditions of R-L sat then we add it)
	//rulesOfLoopsHeads[mminus[k]->inLoop] = AddItem (rulesOfLoopsHeads[mminus[k]->inLoop], rule);

	//  then we will go thru every list and create clauses for each of them
	//  and then delete rulesOfLoopsHeads lists

	//clean up addedInLoop vector in disjunctive rules
	int idSCC = atomsSCC[0]->inLoop;
	vector<Atom*>::iterator itrl;
	list<NestedRule*>::iterator itrNRule;
	if (program.disj) {
		for (itrl = atomsSCC.begin(); itrl != atomsSCC.end(); itrl++) {
			if ((*itrl)->headofDR) {
				//then we go thru all its disj rules and clear the addedInLoop vector
				for (itrNRule = (*itrl)->nestedRules.begin();
						itrNRule != (*itrl)->nestedRules.end(); ++itrNRule) {
					if ((*itrNRule)->sizeHead() > 1)
						(*itrNRule)->addedInLoop = false;
					else
						break;  //at this point all next rules will be nondisj
				}
			}
		}
	}

	NestedRule* r;
	Atom** a;
	bool ruleAdded;
	bool loop;
	bool ruleSat;

	if (atomsSCC.size() == 1)
		//we can empty such loops
		atomsSCC.clear();

	for (int indL = 0; indL < atomsSCC.size(); indL++) {
		for (itrNRule = atomsSCC[indL]->nestedRules.begin();
				itrNRule != atomsSCC[indL]->nestedRules.end(); ++itrNRule) {
			r = (*itrNRule);
			//we would like to add only one disjunctive rule
			//and also go thru disj rule only once
			ruleAdded = false;
			//if rule is disjunctive we take a look
			//whether it was added already for this loop
			//we need to find whether it is within inLoop vector
			if (r->sizeHead() > 1 && r->addedInLoop) {
				ruleAdded = true;
			}

			if (!ruleAdded) {
				//if disjunctive
				if (r->sizeHead() > 1)
					r->addedInLoop = true;
				loop = false;
				ruleSat = true;
				for (a = r->pbody; a != r->pend; a++) {
					if ((*a)->inLoop == idSCC) {
						loop = true;
						break;
					}
				}
				//if the rule is sutable for R-(L)
				//we see if it is also not satisfied by current model
				if (!loop) {
					if (!(*itrNRule)->bodySatisfied())
						ruleSat = false;

					if (ruleSat) {
						for (a = r->head; a != r->hend; a++) {
							if ((*a)->inLoop != idSCC && (*a)->inM) {
								ruleSat = false;
								break;
							}
						}
					}
				}

				if (!loop && !ruleSat) {//if the rule sat conditions of R^-(L)
					//and is unsatisfied by current model
					//we add it to rulesOfLoopsHeads
					rulesOfLoopsHeads.push_back(r);
				} else if (!loop && ruleSat) {//if the rule sat conditions of R^-(L)
					//but is SAT by current rule then
					//current loop formula is SAT and we are not interested in
					//finding its rules
					rulesOfLoopsHeads.clear();
					atomsSCC.clear();	//clean the list of atoms of this loop
					//we exit from current rule loop and
					//we  also then exit current
					// loop of atoms as now loop size is 0
					break;
				}
			}
		}
	}

	return;
}

void Cmodels::buildClausesOfLoopFormula(const vector<Atom*> & atomsSCC,
		const vector<NestedRule*> & rulesOfLoop) {

	//
	//here we build clauses from smallestOrRandLoop
	resetApi();

	if (rulesOfLoop.size() == 0) { //R^-(L) is empty hence the claeses have the form:
		//-p1...&-pn where p1...pn belong to L, i.e. number of unit clauses
		for (int inLoop = 0; inLoop < atomsSCC.size(); inLoop++) {
			add_clause_from_compute(atomsSCC[inLoop], false);
		}
	} else {
		//seem to be too week of a loop hence we will add only single atom out of it
		//here we add loop to api -l1...-l2
		//Now we pick only one atom randomly
		assert(atomsSCC.size() > 1);
		int inLoop = int(atomsSCC.size() * rand() / (RAND_MAX + 1.0));
		api->add_body(atomsSCC[inLoop], false);

		//we eliminate creating auxilary atoms at this stage
		//and instead use reprComp for body of a rule plus the heads multiplication
		//adds atoms to Api body and nbody and once added
		//we create a clause and recursivley recreate api
		//lists again
		int counter = 0;
		atomsMultiplication(rulesOfLoop, rulesOfLoop.size(), 0, counter,
				atomsSCC[0]->inLoop);
		assert(counter <= param.numLFClauses);
		//clear api
		resetApi();

	}

	//    program.print_clauses();

}

inline void Cmodels::clauseFromApi() {
	//here we create a clause out of api
	Clause* cl = new Clause();
	cl->initClauseFromApi(api);
	program.number_of_clauses++;
	program.clauses.push_back(cl);
	cl->finishClause();

}

void Cmodels::atomsMultiplication(const vector<NestedRule*> & rules,
		const int& numRules, int curRule, int & counter, const int& inLoop) {
	if (counter >= param.numLFClauses)
		return;
	Atom* h;
	//
	//in this part we reached then end of the recursin and create clauses
	if (numRules == curRule + 1) {  //we are at the last rule
	//if the rule is not basic OR if the rule does not have representative atom
		bool flag = false;
		if (rules[curRule]->sizeHead() > 1
				|| rules[curRule]->signReprComp == NOT_DEF) {
			int i = 0;
			while (i < rules[curRule]->sizeHead()) {
				h = rules[curRule]->head[i];
				//		if(h->inLoop!=inLoop){//if this atom is in loop we proceed
				//to the next one
				if (h->inM && h->inLoop != inLoop) {//if atom is not in the model
					if (!h->computeTrue && h->inClause != NEG) {
						if (h->inClause == NOT_DEF) {//h is not positive since otherwise
							//h is pos now we would add it negatively to clause
							//and then it be a tautology

							api->add_body(h, false);
							//here we create a clause out of api
							clauseFromApi();
							counter++;
							api->pop_body(false);
							if (counter >= param.numLFClauses)
								return;
						}
					} else {
						if (!flag) {
							clauseFromApi();
							counter++;
							if (counter >= param.numLFClauses)
								return;
							flag = true;
						}
					}

				}
				i++;

			}

			if (rules[curRule]->signReprComp == NOT_DEF) {
				for (Atom** a = rules[curRule]->nbody;
						a < rules[curRule]->nnend; a++) {
					//check if the atom is already in the clause
					//if so add clause without atom (SEE FLAG!)
					//otherwise add atom add clause and drop atom from clause
					if ((*a)->inClause == NOT_DEF) {
						if (a < rules[curRule]->nend)
							api->add_body((*a), false);
						else
							api->add_body((*a), true);
						//here we create a clause out of api
						clauseFromApi();
						counter++;
						if (a < rules[curRule]->nend)
							api->pop_body(false);
						else
							api->pop_body(true);

						if (counter >= param.numLFClauses)
							return;
					} else if (!flag
							&& (((*a)->inClause == NEG
									&& a < rules[curRule]->nend)
									|| ((*a)->inClause == POS
											&& a >= rules[curRule]->nend))) {
						clauseFromApi();
						counter++;
						if (counter >= param.numLFClauses)
							return;
						flag = true;
					}

				}
			}

		}
		//if rule is not fact --FACT CANNOT APPEAR HERE! IT is a LF computation!
		if (rules[curRule]->signReprComp != NOT_DEF) {
			if (rules[curRule]->reprComp->inClause == NOT_DEF) {
				if (rules[curRule]->signReprComp == POS)
					api->add_body(rules[curRule]->reprComp, true);
				else
					api->add_body(rules[curRule]->reprComp, false);
				clauseFromApi();
				counter++;
				if (rules[curRule]->signReprComp == POS)
					api->pop_body(true);
				else
					api->pop_body(false);
				if (counter >= param.numLFClauses)
					return;

			} else if (!flag
					&& rules[curRule]->signReprComp
							== rules[curRule]->reprComp->inClause) {

				clauseFromApi();
				counter++;
				if (counter >= param.numLFClauses)
					return;
			}
		}

		return;
	}
	//
	//here we go recursively till the last rule when we are able to build a clause
	//if rule is not fact
	if (rules[curRule]->signReprComp != NOT_DEF) {
		if (rules[curRule]->reprComp->inClause == NOT_DEF) {
			rules[curRule]->reprComp->ruleId = curRule;
			if (rules[curRule]->signReprComp == POS) {
				rules[curRule]->reprComp->inClause = POS;
				api->add_body(rules[curRule]->reprComp, true);
			} else {
				rules[curRule]->reprComp->inClause = NEG;
				api->add_body(rules[curRule]->reprComp, false);
			}
		}
		if (rules[curRule]->reprComp->inClause
				== rules[curRule]->signReprComp) {
			atomsMultiplication(rules, numRules, curRule + 1, counter, inLoop);
			if (rules[curRule]->reprComp->ruleId == curRule) {
				rules[curRule]->reprComp->inClause = NOT_DEF;
				rules[curRule]->reprComp->ruleId = -1;
				api->pop_body(true);
			}
		}
	}

	//if the rule is not basic
	if (rules[curRule]->sizeHead() > 1
			|| rules[curRule]->signReprComp == NOT_DEF) {
		int i = 0;
		while (i < rules[curRule]->sizeHead()) {
			if (counter >= param.numLFClauses)
				return;

			h = rules[curRule]->head[i];
			//	  if(h->inLoop!=inLoop){
			if (h->inM && h->inLoop != inLoop) {
				if (h->inClause != POS) { //if h is POS we would add it NEG
					//and then clause is a tautology so we do not add this atom and do not
					//recursively go farther!
					//we want to return from recursion on this pass
					if (!h->computeTrue && h->inClause != NEG) {
						api->add_body(h, false);
						h->inClause = NEG;
						h->ruleId = curRule;
					}
					atomsMultiplication(rules, numRules, curRule + 1, counter,
							inLoop);
					if (h->ruleId == curRule) {
						api->pop_body(false);
						h->inClause = NOT_DEF;
						h->ruleId = -1;
					}
				}
			}
			i++;

		}
		if (rules[curRule]->signReprComp == NOT_DEF) {
			for (Atom** a = rules[curRule]->nbody; a < rules[curRule]->nnend;
					a++) {
				//check if the atom is already in the clause
				//if so add clause without atom (SEE FLAG!)
				//otherwise add atom add clause and drop atom from clause
				if ((*a)->inClause == NOT_DEF
						|| ((*a)->inClause == NEG && a < rules[curRule]->nend)
						|| ((*a)->inClause == POS && a >= rules[curRule]->nend)) {
					if ((*a)->inClause == NOT_DEF) {
						if (a < rules[curRule]->nend) {
							api->add_body((*a), false);
							(*a)->inClause = NEG;
						} else {
							api->add_body((*a), true);
							(*a)->inClause = POS;
						}
						(*a)->ruleId = curRule;
					}
					atomsMultiplication(rules, numRules, curRule + 1, counter,
							inLoop);
					if ((*a)->ruleId == curRule) {
						if ((*a)->inClause == POS)
							api->pop_body(true);
						else
							api->pop_body(false);
						(*a)->inClause = NOT_DEF;
						(*a)->ruleId = -1;
					}
				}

			}
		}
	}
}

void Cmodels::createDoubleClause(Atom* firstAtom, Atom* secAtom, bool firstTrue,
		bool secTrue) {
	assert(firstAtom);
	assert(secAtom);
	// we do not need to create a clause
	// if one of its literals is known to be true
	if (firstAtom->Bpos && firstTrue) {
		return;
	}
	if (secAtom->Bpos && secTrue) {
		return;
	}
	if ((firstAtom->Bneg) && !firstTrue) {
		return;
	}
	if ((secAtom->Bneg) && !secTrue) {
		return;
	}
	//we create a unit clause
	//if one of the literals known to be false
	if (firstAtom->Bpos && !firstTrue) {
		api->set_compute(secAtom, secTrue, true);
		return;
	}

	if (secAtom->Bpos && secTrue) {
		api->set_compute(firstAtom, firstTrue, true);
		return;
	}
	if ((firstAtom->Bneg) && firstTrue) {
		api->set_compute(secAtom, secTrue, true);
		return;
	}
	if ((secAtom->Bneg) && secTrue) {
		api->set_compute(firstAtom, firstTrue, true);
		return;
	}

	//here we create a clause with two literals
	//
	Clause *cl = new Clause();		//will be -head v head
	if (firstTrue && secTrue) {
		cl->allocateClause(0, 2);
		cl->addPbody(0, firstAtom);
		cl->addPbody(1, secAtom);
	} else if (firstTrue && !secTrue) {
		cl->allocateClause(1, 1);
		cl->addPbody(0, firstAtom);
		cl->addNbody(0, secAtom);
	} else if (!firstTrue && secTrue) {
		cl->allocateClause(1, 1);
		cl->addNbody(0, firstAtom);
		cl->addPbody(0, secAtom);
	} else if (!firstTrue && !secTrue) {
		cl->allocateClause(2, 0);
		cl->addNbody(0, firstAtom);
		cl->addNbody(1, secAtom);
	}
	program.number_of_clauses++;
	program.clauses.push_back(cl);
	cl->finishClause();
	//  cl->print();
}

void Cmodels::printCycles(const int& numSCC) {
	//array of vector of atoms that belong to some loop
	vector<Atom*>* atomsSCC = new vector<Atom*> [numSCC];
	//he we intialize the vector
	for (vector<Atom*>::iterator itrmm = program.atoms.begin();
			itrmm != program.atoms.end(); itrmm++)
		if ((*itrmm)->inLoop != -1) {
			atomsSCC[(*itrmm)->inLoop].push_back((*itrmm));
		}
	for (int i = 0; i < numSCC; i++) {
		cout << "Cycle: ";
		for (vector<Atom*>::iterator itrmm = atomsSCC[i].begin();
				itrmm != atomsSCC[i].end(); itrmm++) {
			(*itrmm)->print();
			cout << " ";
			//				printRules(*itrmm);
		}
		cout << endl;
	}
	delete[] atomsSCC;
}

void Cmodels::printReason(int* assignment, int found) {
	printf("Reason: %d \n Clause: ", found);

	for (vector<Atom*>::iterator itrAtom = program.atoms.begin();
			itrAtom != program.atoms.end(); ++itrAtom) {

		if (assignment[(*itrAtom)->id - 1] == 1) {
			(*itrAtom)->print();
			cout << " ";
		} else if (assignment[(*itrAtom)->id - 1] == 2) {
			cout << "-";
			(*itrAtom)->print();
			cout << " ";

		}
	}
	printf("\n");
}
void Cmodels::printSolution(bool* assignment, int found) {
	printf("Assignment: %d \n ", found);

	for (vector<Atom*>::iterator itrAtom = program.atoms.begin();
			itrAtom != program.atoms.end(); ++itrAtom) {

		if (assignment[(*itrAtom)->id - 1]) {
			(*itrAtom)->print();
			cout << " ";
		}
	}
	printf("\n");
}


inline void Cmodels::translateClauseToReason(int* reason, int & reasonSize) {
	//at this point it should be not greater than 1

	int clId = int(program.clauses.size() * rand() / (RAND_MAX + 1.0));
	program.clauses[clId]->translateToSimoReason(reason, reasonSize,
			program.number_of_atoms);
	for (int i = 0; i < program.clauses.size(); i++)
		delete program.clauses[i];
	program.clauses.clear();

}

void Cmodels::addReasonClause(int* reason) {

	Clause* cl = new Clause();
	resetApi();
	//there cannot be more atoms in reason as
	// only atoms that belong to rules
	// can be part of this clause
	for (long indA = 0; indA < program.cmodelsAtomsFromThisId; indA++) {
		if (reason[program.atoms[indA]->id - 1] == 1) {
			api->add_body(program.atoms[indA], true);
		} else if (reason[program.atoms[indA]->id - 1] == 2) {
			api->add_body(program.atoms[indA], false);
		}
	}

	cl->initClauseFromApi(api);
	cl->finishClause();
	program.number_of_clauses++;
	program.clauses.push_back(cl);
	resetApi();
}


//returns false if the constraint is inconsistent with the database
//of clauses
bool Cmodels::addDenial(int* constraint_lits, int num_lits) {
	int* reason = new int[program.number_of_atoms];
	//here we convert constraint_lits into assignments
	bool ret = true;

	for (int i = 0; i < program.number_of_atoms; i++) {
		reason[i] = 0; //by default atom is not in the reason
	}

	//  populate_assignment_with_denial(constraint_lits,num_lits,assignments);
	//we need to go through the list of denial atoms
	//and for each find a corresponding atom in
	int cur;
	bool cur_sign;
	int inner_count = 0;
	long indA = 0;
	for (int i = 0; i < num_lits; i++) {
		if (constraint_lits[i] % 2) {  //if it is odd
			cur = (constraint_lits[i] - 1) / 2;
			cur_sign = true;
		} else {
			cur = constraint_lits[i] / 2;
			cur_sign = false;
		}

		for (indA = inner_count; indA < program.cmodelsAtomsFromThisId;
				indA++) {

			if (cur == program.atoms[indA]->get_lparse_id()) {

				if (cur_sign)
					reason[indA] = 1;
				else
					reason[indA] = 2;
				break;
			}
		}
		if (indA == program.cmodelsAtomsFromThisId - 1 && i != num_lits - 1) {
			cerr
					<< "Cmodels: Error with denial addition (one of the denial atoms was eliminated as false)";
			exit(20);
		}

	}

	//adding reason to clause database of cmodels
	//    printReason(reason, 1);
	addReasonClause(reason);


	delete[] reason;
	return ret;
}



void Cmodels::setupFilenames() {

	/* initialize random seed: */
	srand(time(NULL));

	sprintf(param.dimacsFileName, "%s%s%d%s", param.dirName,
			"dimacs-completion", rand(), ".out");
	sprintf(param.solverOutputFileName, "%s%s%d%s", param.dirName,
			"solver-solution", rand(), ".out" "%s%s", param.dirName);

	FILE* fconfig = NULL;
	fconfig = fopen(param.config, "r");
	int count = -10;
	char s1[1024], s2[1024], chaffCommand[1024];
	char relsat_loc[1024] = "./relsat";
	char zchaff_loc[1024] = "./zchaff";
	char bcircuit_loc[1024] = "./bcircuit ";
	bool config_exist = true;
	char path_to_config[1024];
	bool empty_path = true;
	if (fconfig == NULL) {
		config_exist = false;

		if (param.sys == RELSAT || param.sys == ASSAT_ZCHAFF)
			if (output.asparagus == STANDARD)
				cerr << "Warning: Config file " << param.config
						<< " is not found, current directory is a default directory for solvers and option files "
						<< endl;

		char path_to_cmodels[100];
		int k = 0;
		path_to_cmodels[k] = '\0';
		int length = strlen(param.cmodelsname);
		int l = length - 1;
		while (l != -1 && param.cmodelsname[l] != '/') {
			l--;
		}
		if (l >= 0) {
			for (k = 0; k <= l; k++)
				path_to_cmodels[k] = param.cmodelsname[k];
			path_to_cmodels[k] = '\0';
		}
		if (param.sys == RELSAT) {
			strcpy(relsat_loc, path_to_cmodels);
			strcat(relsat_loc, "relsat");
		} else {
			strcpy(zchaff_loc, path_to_cmodels);
			strcat(zchaff_loc, "zchaff");
		}
	} else {
		int length = strlen(param.config);
		int l = length - 1;
		while (l != -1 && param.config[l] != '/') {
			l--;
		}
		if (l < 0)
			empty_path = true;
		else {
			empty_path = false;
			int k;
			for (k = 0; k <= l; k++)
				path_to_config[k] = param.config[k];
			path_to_config[k] = '\0';
		}

		char temp[1024];

		bool flag4relsat = false;
		bool flag4zchaff = false;

		while (count != EOF) {
			count = fscanf(fconfig, "%s", &temp[0]);
			if (!strcmp(temp, "relsat")) {
				count = fscanf(fconfig, "%s", &relsat_loc[0]);
				flag4relsat = true;
			}
			if (!strcmp(temp, "zchaff")) {
				count = fscanf(fconfig, "%s", &zchaff_loc[0]);
				flag4zchaff = true;
			}
		}
		if (!flag4relsat && param.sys == RELSAT) {
			if (output.asparagus == STANDARD)
				cout << "Warning: Location of relsat  is not specified in "
						<< param.config
						<< " file and default value ./relsat is taken" << endl;
		}
		if (!flag4zchaff && param.sys == ASSAT_ZCHAFF) {
			if (output.asparagus == STANDARD)
				cout << "Warning: Location of zchaff  is not specified in "
						<< param.config
						<< " file and default value ./zchaff is taken" << endl;
		}

		if (!empty_path) {
			bool path_spec = false;
			length = strlen(relsat_loc);
			for (int k = 0; k < length; k++) {
				if (relsat_loc[k] == '/') {
					path_spec = true;
				}
			}
			if (!path_spec) {
				char str2[1024];
				strcpy(str2, path_to_config);
				strcat(str2, relsat_loc);
				strcpy(relsat_loc, str2);
			}
		}

		fclose(fconfig);

	}
	char strtmp[1024];
	unlink(param.solverOutputFileName);

	//
	//End of a portion which is responsible for
	//naming all the files correctly
	//

	//command line for RELSAT
	if (param.sys == RELSAT) {
		char s[1024];
		if (!program.tight)
			sprintf(s, "%s -#%d %s > %s ", relsat_loc, 1, param.dimacsFileName,
					param.solverOutputFileName);
		else if (param.many != 0)
			sprintf(s, "%s -#%d %s > %s ", relsat_loc, param.many,
					param.dimacsFileName, param.solverOutputFileName);
		else
			sprintf(s, "%s -#a %s > %s ", relsat_loc, param.dimacsFileName,
					param.solverOutputFileName);
		strcpy(command, s);

	}
	//command line for ASSAT_ZCHAFF
	if (param.sys == ASSAT_ZCHAFF) {
		char s[1024];
		sprintf(s, "%s %s > %s ", zchaff_loc, param.dimacsFileName,
				param.solverOutputFileName);
		strcpy(command, s);

	}

	//command line for BCircuit
	if (param.sys == BCIRCUIT) {
		char s[1024];
		sprintf(s, "%s %s > %s", bcircuit_loc, param.dimacsFileName,
				param.solverOutputFileName);
		strcpy(command, s);
	}

}


//
//Weight rules translation
//

bool Cmodels::rec_weight_rule(Weight totalweight, int sizeC, Atom* headC,
		unsigned long atleast, int counter_body) {

	if (atleast > totalweight) { //no way to sat the recuirement

		api->set_compute(headC, false, true);

		return false;
	} else if (sizeC == 0) { //case when sizeC is empty

		api->set_compute(headC, false, true);

		return false;
	} else {
		long curw = api->getPbodyWeights(counter_body);

		if (counter_body < api->sizeNbody()) {
			curw = api->getNbodyWeights(counter_body);

		} else {
			int pcounter = -api->sizeNbody() + counter_body;
			curw = api->getPbodyWeights(pcounter);
		}
		long newtw = (unsigned long) (unsigned long) totalweight
				- (unsigned long) curw;

		if (newtw >= atleast) {

			//case  when there is need to create a new rule
			NestedRule *r = new NestedRule();
			r->type = BASICRULE;
			Atom * acopy = headC;

			acopy->addToRuleList(r);
			r->allocateRule(1, 0, 1);
			r->addHead(0, acopy);

			char* stotal = new char[128];
			//BUG fixed in version 3.79
			//	  sprintf(stotal,"%ldx%ld",atleast,newtw);
			//replaced by:
			sprintf(stotal, "%ldx%ldx%ld", atleast, newtw, counter_body + 1);
			Atom* at1 = api->wrmem.findAtom(stotal);
			if (at1 == NULL) {
				at1 = api->new_atom();
				api->wrmem.addAtom(at1, stotal);
				rec_weight_rule((unsigned long) totalweight - curw, sizeC - 1,
						at1, atleast, counter_body + 1);
			} else {
				delete[] stotal;
			}

			r->addPbody(0, at1);
			r->finishRule();
		}
		long newatleast = (unsigned long) (unsigned long) atleast
				- (unsigned long) curw;
		int n;
		if (newatleast > 0 && newatleast <= newtw)
			n = 2;
		else if (newatleast <= 0)
			n = 1;
		else {

			return false;//case of false atom in the body so no need to creat rule
		}

		NestedRule *rcopy = new NestedRule();
		rcopy->type = BASICRULE;
		Atom * acopy = headC;
		acopy->addToRuleList(rcopy);

		if (!api->pbody.np[counter_body]) {	//counter_body<api->sizeNbody()){
			rcopy->allocateRule(1, 1, n - 1);
			rcopy->addNbody(0, api->pbodyAtom(counter_body));
		} else {
			rcopy->allocateRule(1, 0, n);
			rcopy->addPbody(0, api->pbodyAtom(counter_body));
		}
		rcopy->addHead(0, acopy);
		if (newatleast > 0 && newatleast <= newtw) {
			char* stotal = new char[128];
			//BUG fixed in version 3.79
			//	  sprintf(stotal,"%ldx%ld",newatleast,newtw);
			//replaced by:
			sprintf(stotal, "%ldx%ldx%ld", newatleast, newtw, counter_body + 1);
			Atom* at2 = api->wrmem.findAtom(stotal);

			if (at2 == NULL) {
				at2 = api->new_atom();
				api->wrmem.addAtom(at2, stotal);
				rec_weight_rule((unsigned long) totalweight - curw, sizeC - 1,
						at2, newatleast, counter_body + 1);
			} else {
				delete[] stotal;
			}
			if (rcopy->sizeNbody() == 0)
				rcopy->addPbody(1, at2);
			else
				rcopy->addPbody(0, at2);
		}
		rcopy->finishRule();

	}
	return false;

}

void Cmodels::buildReduct() {
	Atom *curAtom;
	for (long indA = 0; indA < program.cmodelsAtomsFromThisId; indA++) {
		curAtom = program.atoms[indA];
		(curAtom)->cons = false;
		if (((curAtom)->choiceruleSpecified && (curAtom)->inM)
				|| curAtom->Bpos) {
			//we don't have to go thru other rules we already know 
			//that this atom is cons since one of the bodies is empty

			(curAtom)->cons = true;
		} else if (!(curAtom)->inM) {
			//do nothing and go to the next atom
		} else {
			NestedRule* br;
			for (list<NestedRule*>::iterator itrNRule =
					curAtom->nestedRules.begin();
					itrNRule != curAtom->nestedRules.end(); ++itrNRule) {
				br = (*itrNRule);
				if (br->nbody == br->end) {
					//we don't have to go thru other rules we already know
					//that this atom is cons since one of the bodies is empty
					(curAtom)->cons = true;
					break;
				}
				br->erased = false;
				//rule is erased when it is not sat by the model
				if (!br->bodySatisfied())
					br->erased = true;
				if (!br->erased && br->pbody == br->pend) {
					//we don't have to go thru other rules we already know
					//that this atom is cons since its positive body is empty and
					//rule is not erased
					if (br->sizeHead() == 1)
						(curAtom)->cons = true;
					break;
				}
			}
		}

	}
}
void Cmodels::printRules() {
	cout << "NESTED RULES OF PROGRAM";

	for (long indA = 0; indA < program.number_of_atoms; indA++) {
		Atom* curAtom = program.atoms[indA];
		for (list<NestedRule*>::iterator itrNRule =
				curAtom->nestedRules.begin();
				itrNRule != curAtom->nestedRules.end(); ++itrNRule) {
			(*itrNRule)->print();
		}
	}

}

void Cmodels::printRules(Atom* a) {
	cout << "NESTED RULES OF Atom ";
	a->print();
	cout << endl;
	for (list<NestedRule*>::iterator itrNRule = a->nestedRules.begin();
			itrNRule != a->nestedRules.end(); ++itrNRule) {
		(*itrNRule)->print();
	}
	cout << "NESTED RULES In Body Atom ";
	cout << endl;
	for (list<NestedRule*>::iterator itrNRule = a->pBodyRules.begin();
			itrNRule != a->pBodyRules.end(); ++itrNRule) {
		(*itrNRule)->print();
	}

}
void Cmodels::printRules(vector<NestedRule*>& rules) {
	cout << "NESTED RULES from vector";
	cout << endl << "Size " << rules.size();
	cout << endl;
	for (vector<NestedRule*>::iterator itrNRule = rules.begin();
			itrNRule != rules.end(); ++itrNRule) {
		(*itrNRule)->print();
	}

}
void Cmodels::printAtoms(vector<Atom*>& atoms) {
	cout << "Atoms ";
	cout << endl << "Size " << atoms.size();
	cout << endl;
	for (vector<Atom*>::iterator itrNRule = atoms.begin();
			itrNRule != atoms.end(); ++itrNRule) {
		(*itrNRule)->print();
		cout << " ";
		//	printRules((*itrNRule));
	}
	cout << endl;

}
void Cmodels::printAtoms(list<Atom*>& atoms) {
	cout << "Atoms ";
	cout << endl << "Size " << atoms.size();
	cout << endl;
	for (list<Atom*>::iterator itrNRule = atoms.begin();
			itrNRule != atoms.end(); ++itrNRule) {
		(*itrNRule)->print();
		cout << " ";
		//(*itrNRule)->printNestedRules();
		//	printRules((*itrNRule));
	}
	cout << endl;

}

void Cmodels::findCons() {
	bool changes = true;
	Atom* curAtom;
	NestedRule* br;
	while (changes) {
		//till we reach fixed point
		changes = false;
		for (long indA = 0; indA < program.cmodelsAtomsFromThisId; indA++) {
			curAtom = program.atoms[indA];
			if (!(curAtom)->nestedRules.size() || (curAtom)->cons
					|| !(curAtom)->inM || (curAtom)->choiceruleSpecified) {
				//do nothing and lets go to the other atom -
			} else {
				for (list<NestedRule*>::iterator itrNRule =
						curAtom->nestedRules.begin();
						itrNRule != curAtom->nestedRules.end(); ++itrNRule) {
					br = (*itrNRule);
					if (!br->erased) {
						bool sat = true;
						for (Atom **a = br->pbody; a != br->pend; a++) {
							if (!(*a)->cons) {
								sat = false; //here we want to go to next rule
								break;
							}
						}
						if (sat) {
							(curAtom)->cons = true; //now we d like to go to next atom
							changes = true;
							break;
						}
					}
					if ((curAtom)->cons)
						break; //the atom is cons so we
					//can go to next atom
				}
			}

		}
	}		       //here we reached fixed ppoint and now need to check wheather
	//there is some atom->inM which is not atom->cons

	/* optimized buggy version
	 bool  changes = true;
	 Atom* curAtom;
	 NestedRule* br;
	 Atom::change=true;
	 while(Atom::change){
	 //till we reach fixed point
	 Atom::setChangeFalse();
	 for(long indA=0; indA<program.cmodelsAtomsFromThisId; indA++){
	 curAtom=program.atoms[indA];
	 if(!(curAtom)->nestedRules.size() || (curAtom)->cons ||
	 !(curAtom)->inM  ||  (curAtom)->choiceruleSpecified)
	 {
	 //do nothing and lets go to the other atom -
	 }
	 else{
	 for (list<NestedRule*>::iterator itrNRule =
	 curAtom->nestedRules.begin();
	 itrNRule !=  curAtom->nestedRules.end();
	 ++itrNRule){
	 br= (*itrNRule);
	 if(!br->erased&&br->pbodyCount==0){
	 curAtom->setConsTrue ();
	 break;
	 }
	 if((curAtom)->cons) break; //the atom is cons so we
	 //can go to next atom
	 }
	 }

	 }
	 }//here we reached fixed ppoint and now need to check wheather
	 //there is some atom->inM which is not atom->cons
	 */
}

void Cmodels::printCons() {
	cout << endl << "Cons: ";
	int atomsTill = 0;
	for (vector<Atom*>::iterator itrAtom = program.atoms.begin();
			itrAtom != program.atoms.end(); ++itrAtom) {
		if ((*itrAtom)->cons) {
			(*itrAtom)->print();
			cout << " ";
		}
	}
	cout << endl;
}

void Cmodels::printM() {

	cout << endl << "M: ";
	int atomsTill = 0;
	for (vector<Atom*>::iterator itrAtom = program.atoms.begin();
			itrAtom != program.atoms.end(); ++itrAtom) {
		if ((*itrAtom)->inM) {
			(*itrAtom)->print();
			cout << " ";
		}

	}
	cout << endl;
}
void Cmodels::printWFM() {

	cout << endl << "POS: ";
	for (vector<Atom*>::iterator itrAtom = program.atoms.begin();
			itrAtom != program.atoms.end(); ++itrAtom) {
		if ((*itrAtom)->Bpos) {
			(*itrAtom)->printClean();

		}

	}

	cout << endl << "NEG: ";
	for (vector<Atom*>::iterator itrAtom = program.atoms.begin();
			itrAtom != program.atoms.end(); ++itrAtom) {
		if ((*itrAtom)->Bneg) {
			(*itrAtom)->printClean();
		}

	}

	cout << endl << "Cons: ";
	for (vector<Atom*>::iterator itrAtom = program.atoms.begin();
			itrAtom != program.atoms.end(); ++itrAtom) {
		if ((*itrAtom)->computeTrue && !(*itrAtom)->Bpos) {
			(*itrAtom)->printClean();

		}

	}
	cout << endl;
}

void Cmodels::printMminus() {

	cout << endl << "Mminus: ";
	int atomsTill = 0;
	for (vector<Atom*>::iterator itrAtom = program.atoms.begin();
			itrAtom != program.atoms.end(); ++itrAtom) {
		if ((*itrAtom)->inMminus) {
			(*itrAtom)->print();
			cout << " ";
		}

	}
	cout << endl;
}

bool Cmodels::solutionVerification(bool* assignment, list<Atom*>& mminus) {

	//
	//process of building a reduct
	//

	buildReduct();

	//here reduct is already built and the atoms which are facts are already known
	//now we want to find CONS of a reduct and see if it is the same as
	//a model of completion
	findCons();

	bool ret = true;

	for (long indA = 0; indA < program.cmodelsAtomsFromThisId; indA++) {
		if (program.atoms[indA]->inM && !program.atoms[indA]->cons) {
			ret = false;  //not answer set
			break;
		}
	}
	if (!ret) {
		findMminus();
		getMminus(mminus);
	}
	return ret;
}

void Cmodels::findMminus(bool* assignment) {

	if (assignment) {
		for (long indA = 0; indA < program.cmodelsAtomsFromThisId; indA++) {
			if (assignment[indA]) {
				program.atoms[indA]->inMminus = true;
			} else
				program.atoms[indA]->inMminus = false;
		}
	} else {
		for (long indA = 0; indA < program.cmodelsAtomsFromThisId; indA++) {
			if (program.atoms[indA]->inM && !program.atoms[indA]->cons) {
				program.atoms[indA]->inMminus = true;
			} else
				program.atoms[indA]->inMminus = false;

		}
	}
}
bool Cmodels::hcfTest(bool* assignment, list<Atom *>& mminus) {

	findMminus(assignment);
	getMminus(mminus);
	aproxMminus(mminus);
	if (mminus.size() == 0)
		return true;
	else
		return false;
}

void Cmodels::markInMminus(list<Atom*>& mminusAtoms) {
	for (list<Atom*>::iterator itrAtom = mminusAtoms.begin();
			itrAtom != mminusAtoms.end(); ++itrAtom)
		(*itrAtom)->inMminus = true;

}
void Cmodels::markInMminus(vector<Atom*>& mminusAtoms) {
	for (vector<Atom*>::iterator itrAtom = mminusAtoms.begin();
			itrAtom != mminusAtoms.end(); ++itrAtom)
		(*itrAtom)->inMminus = true;

}

void Cmodels::markAtomsInSccInM(const int& idScc) {
	//set default
	for (long indA = 0; indA < program.cmodelsAtomsFromThisId; indA++) {
		if (program.atoms[indA]->inLoop == idScc)
			program.atoms[indA]->inM = true;
		else
			program.atoms[indA]->inM = false;
	}
}

//for disjunctive programs
//approximation of Mminus 
//takes original list of atoms mminusAtoms 
//and converges it to approximate mminus
void Cmodels::aproxMminus(list<Atom*>& mminusAtoms) {
	list<int> deleted;
	list<Atom*>::iterator itrAtom;
	list<int>::iterator itrI;
	while (true) {
		itrAtom = mminusAtoms.begin();
		while (itrAtom != mminusAtoms.end()) {
			if ((*itrAtom)->choiceruleSpecified || (*itrAtom)->Bpos
					|| !dlvOperatorCondition((*itrAtom))) {
				deleted.push_back((*itrAtom)->id - 1);
				itrAtom = mminusAtoms.erase(itrAtom);
			} else
				itrAtom++;
		}

		if (deleted.size() == 0)  //we converged
			return;
		else {
			//mark atoms in deleted as not inMminus and
			//clear the list
			for (itrI = deleted.begin(); itrI != deleted.end(); ++itrI)
				program.atoms[(*itrI)]->inMminus = false;
			deleted.clear();
		}
	}
}
//traverses rules of atoms to see if
//conditions of belonging to Operator are SAT
bool Cmodels::dlvOperatorCondition(Atom* atom) {
	Atom **a;
	bool ret = false;
	bool satisf = false;

	for (list<NestedRule*>::iterator itrNRule = atom->nestedRules.begin();
			itrNRule != atom->nestedRules.end(); ++itrNRule) {
		satisf = false;
		if ((*itrNRule)->sizeHead() > 1) {	  //disj rule
			for (a = (*itrNRule)->head; a < (*itrNRule)->hend; a++)
				if ((*a)->inM && (*a)->id != atom->id) {
					satisf = true;
					break;
				}
		}
		if (!satisf) {	  //if the rule does not sat conditions
			//yet we need to go thru body to see
			//whether it is non sat and also whether its part of pbody is inM
			if (!(*itrNRule)->bodySatisfied())
				satisf = true;

			if (!satisf) {
				for (a = (*itrNRule)->pbody; a < (*itrNRule)->pend; a++)
					if ((*a)->inMminus) {
						satisf = true;
						break;
					}
			}
		}
		if (!satisf)	  //rule does not satify condition
			//so we return false
			return false;
	}
	return true;
}
/*
 void
 Cmodels::markAtomsInSCCInM(vector<Atom*>& atomsSCC){
 //set default
 clearInM();
 for(long indA=0; indA!=atomsSCC.size();indA++)
 atomsSCC[indA]->inM=true;

 }
 */

void Cmodels::markAtomsInM(bool *sol) {
	for (long indA = 0; indA < program.atoms.size(); indA++) {
		if (sol[indA]) {
			program.atoms[indA]->inM = true;
		} else {
			program.atoms[indA]->inM = false;
		}
	}

}

void Cmodels::markAtomsInCons(vector<Atom*> &atomsSCC, bool *consDisj) {
	for (long indA = 0; indA < atomsSCC.size(); indA++)
		if (consDisj[indA]) {
			atomsSCC[indA]->cons = true;
		}
}
void Cmodels::markAtomsInCons(bool *consDisj) {

	for (long indA = 0; indA < program.atoms.size(); indA++) {
		if (consDisj[indA])
			program.atoms[indA]->cons = true;
		else
			program.atoms[indA]->cons = false;
	}
}
void Cmodels::clearAtomsInCons(vector<Atom*> &atomsSCC) {

	for (long indA = 0; indA < atomsSCC.size(); indA++)
		atomsSCC[indA]->cons = false;

}
void Cmodels::setInLoopId(vector<Atom*> &atomsSCC) {
	for (long indA = 0; indA < atomsSCC.size(); indA++)
		atomsSCC[indA]->inLoopId = indA + 1;
}


void Cmodels::getMminus(list<Atom*>& Mminus) {
	for (long indA = 0; indA < program.cmodelsAtomsFromThisId; indA++) {
		if (program.atoms[indA]->inMminus) {
			Mminus.push_back(program.atoms[indA]);

		}
	}
}

void Cmodels::findLFReason(bool* assignment, int* reason, int& reasonSize,
		list<Atom *>& mminus, int* modes) {

	//if not an answer set we need to find MMinus
	//and find Maximal Loop
	//and build a loop formula

	reasonSize = 0;
	assert(mminus.size() > 0);
	if (param.loopFormula || param.le || param.bj) {

		LoopFormulaComputation(reason, reasonSize, mminus, modes);
	} else {  //backtracking is enforced so a reason
		//is a negated model
		reasonSize = program.cmodelsAtomsFromThisId;
		for (int k = 0; k < program.cmodelsAtomsFromThisId; k++) {
			if (assignment[k])
				reason[k] = 2;
			else if (!program.basic)
				reason[k] = 1;
		}

	}

}

//here we would like to make random choice of which reason to add
//from which LF, unless shortest reason is needed
void Cmodels::buildReasonFromLoops(const vector<Atom*>&atomsSCC, int* reason,
		const vector<NestedRule*>& rulesOfLoop, const int& inLoop, int* modes) {

	//
	//here we build our disj. clause
	//in each of the bodies of rules
	//we find the atom which is not inM (in the cur Model
	//and add it to reason clause
	//this way we will get unsatisfied clause by the current Model
	//and clause which is in following relation with loop formula
	// loop_formula  implies clause
	//we also do it only for 1 SCC, such that it is not sat by current model

	for (int i = 0; i < program.number_of_atoms; i++) {
		reason[i] = 0; //by default atom is not in the reason
	}
	int place = -1;
	int bestPlace = -1;

	for (int indAinLoop = 0; indAinLoop < atomsSCC.size(); indAinLoop++) {
		place = atomsSCC[indAinLoop]->id - 1;
		if (bestPlace == -1)
			bestPlace = place;
		if (!modes)
			break;
		else if (modes[place] < modes[bestPlace])
			bestPlace = place;
	}
	assert(bestPlace != -1);
	reason[bestPlace] = 2;

	//rightSCC is taken care before when we build nes. rules
	// bool rightSCC= true; //if it is false after
	//we get out of the follwoing cicle then we need to perform it again
	//for a new SCC

	NestedRule * r;
	bool notFound;
	int value;
	for (long indNR = 0; indNR < rulesOfLoop.size(); indNR++) {
		r = rulesOfLoop[indNR];

		notFound = true;
		//here we need to go thru all literals in the body and head!=L and
		//find one which is not in the model
		bestPlace = -1;

		for (Atom **a = r->head; a != r->nend; a++) {
			if ((*a)->inLoop != inLoop && (*a)->inM) {
				place = (*a)->id - 1;
				notFound = false;
				if (bestPlace == -1) {
					bestPlace = place;
					value = 2;
				}
				if (!modes)
					break;
				else if (modes[place] < modes[bestPlace]) {
					bestPlace = place;
					value = 2;
				}
			}
		}
		if (notFound || modes) {
			for (Atom **a = r->pbody; a != r->nnend; a++) {
				if (!(*a)->inM) {
					place = (*a)->id - 1;
					if (bestPlace == -1) {
						value = 1;
						bestPlace = place;
					}
					notFound = false;
					if (!modes)
						break;
					else if (modes[place] < modes[bestPlace]) {
						value = 1;
						bestPlace = place;
					}
				}
			}
		}
		if (notFound || modes) {
			for (Atom **a = r->nbody; a != r->nend; a++) {
				if ((*a)->inM) {
					place = (*a)->id - 1;
					if (bestPlace == -1) {
						value = 2;
						bestPlace = place;
					}
					notFound = false;
					if (!modes)
						break;
					else if (modes[place] < modes[bestPlace]) {
						value = 2;
						bestPlace = place;
					}
				}
			}
		}
		assert(bestPlace != -1);
		reason[bestPlace] = value;
	}

}

void Cmodels::buildGraphsCCandReverse(list<Atom*> & mminus,
		const bool & wrtModel) {
	if (!wrtModel) {
		for (list<Atom*>::iterator itrmm = mminus.begin();
				itrmm != mminus.end(); itrmm++) {

			if (!(*itrmm)->choiceruleSpecified) {
				for (list<NestedRule*>::iterator itrNRule =
						(*itrmm)->nestedRules.begin();
						itrNRule != (*itrmm)->nestedRules.end(); ++itrNRule) {
					for (Atom **a = (*itrNRule)->pbody; a != (*itrNRule)->pend;
							a++) {
						if ((*a)->inMminus)
							grCC->addEdge((*itrmm)->id, (*a)->id);

					}
				}
			}
		}

	} else {

		for (list<Atom*>::iterator itrmm = mminus.begin();
				itrmm != mminus.end(); itrmm++)
			if (!(*itrmm)->choiceruleSpecified) {
				for (list<NestedRule*>::iterator itrNRule =
						(*itrmm)->nestedRules.begin();
						itrNRule != (*itrmm)->nestedRules.end(); ++itrNRule) {
					if ((*itrNRule)->bodySatisfied())//if the body is SAT by the model
						for (Atom **a = (*itrNRule)->pbody;
								a != (*itrNRule)->pend; a++) {
							if ((*a)->inMminus)
								grCC->addEdge((*itrmm)->id, (*a)->id);
						}
				}
			}
	}

}
void Cmodels::buildCompletePosNegGr(list<Atom*> & mminus) {
	for (list<Atom*>::iterator itrmm = mminus.begin(); itrmm != mminus.end();
			itrmm++)
		for (list<NestedRule*>::iterator itrNRule =
				(*itrmm)->nestedRules.begin();
				itrNRule != (*itrmm)->nestedRules.end(); ++itrNRule) {
			for (Atom **a = (*itrNRule)->nbody; a != (*itrNRule)->nnend; a++) {
				if ((*a)->inMminus)
					grCC->addEdge((*itrmm)->id, (*a)->id);
			}
		}

}

//
//find connected components
//
void Cmodels::findSCC(long * atomCC, list<Atom*>& mminus, long & numSCC,
		bool posDependency, const bool &wrtModel) {
	grCC = new Graph();
	if (posDependency)
		buildGraphsCCandReverse(mminus, wrtModel);
	else
		buildCompletePosNegGr(mminus);
	grCC->SCC(atomCC, numSCC);
	delete grCC;
}

void Cmodels::addAssignmentClause(bool* assignments) {

	resetApi();
	//it is enough to add only guys from before clausification
	//as the othe rones can be infered from the clause
	for (long indA = 0; indA < program.cmodelsAtomsFromThisId; indA++) {
		if (assignments[indA])
			api->add_body(program.atoms[indA], false);
		else if (!program.basic)  //if program is basic we can add
			//smaller clauses
			api->add_body(program.atoms[indA], true);

	}
	Clause *cl = new Clause();
	cl->initClauseFromApi(api);
	program.number_of_clauses++;
	program.clauses.push_back(cl);
	cl->finishClause();
	resetApi();

}

// based on set of atoms in mminus, 
// finds SCC in induced positive dependency graph by Mminus
// marks such atoms in their .inLoop
// and returns number of SCC 
//  
void Cmodels::enumMarkSCC(list<Atom*>& mminus, long & numSCC,
		bool posDependency, bool wrtModel) {
	long* atomsCC = new long[program.cmodelsAtomsFromThisId + 1];
	atomsCC[0] = -1;
	long size = mminus.size();

	for (list<Atom*>::iterator itrmm = mminus.begin(); itrmm != mminus.end();
			itrmm++)
		atomsCC[(*itrmm)->id] = -1;

	findSCC(atomsCC, mminus, numSCC, posDependency, wrtModel);
	if (numSCC == 0)
		return;

	for (list<Atom*>::iterator itrmm = mminus.begin(); itrmm != mminus.end();
			itrmm++) {
		(*itrmm)->inLoop = atomsCC[(*itrmm)->id];
	}

	delete[] atomsCC;
}

// function computes loop formula or reason based on:
// assignment, atoms within which mminus is located (mminus)
// it stores reason and reasonsize in the corresponding arguments

void Cmodels::LoopFormulaComputation(int* reason, int & reasonSize,
		list<Atom*>& mminus, int* modes) {

	reasonSize = 0;
	long numSCC = 0;
	clearInLoop();
	enumMarkSCC(mminus, numSCC, true);

	assert(numSCC > 0);

	//here we define lists corresponding to R-(L) rules
	vector<NestedRule*>* rulesOfLoopsHeads = new vector<NestedRule*> [numSCC];
	list<vector<Atom*> > elSets;
	vector<NestedRule*>* rulesOfEsets = 0;
	//array of vector of atoms that belong to some loop
	vector<Atom*>* atomsSCC = new vector<Atom*> [numSCC];
	//he we intialize the vector
	for (list<Atom*>::iterator itrmm = mminus.begin(); itrmm != mminus.end();
			itrmm++)
		if ((*itrmm)->inLoop != -1) {
			atomsSCC[(*itrmm)->inLoop].push_back((*itrmm));
		}

	//already at finding loopRules we only find these for which loop
	//formula is not SATisfied
	loopRulesInit(numSCC, atomsSCC, rulesOfLoopsHeads);

	int smallestOrRandLoop = -1;
	if (!param.shortr) {  //then we pick loop randomply

		long temp = long(numSCC * rand() / (RAND_MAX + 1.0));

		if (atomsSCC[temp].size() == 0) {
			//we need to go thru loops and take the closest to it
			//first we go back then we go from
			int copySm = temp;
			for (int indA = temp; indA >= 0; indA--) {
				if (atomsSCC[indA].size() > 0) {
					temp = indA;
					break;
				}
			}
			if (copySm == temp) {	//smallestLoop is still not the right one
				for (int indA = temp + 1; indA < numSCC; indA++) {
					if (atomsSCC[indA].size() > 0) {
						temp = indA;
						break;
					}
				}
			}
			if (copySm != temp)
				smallestOrRandLoop = temp;
		} else
			smallestOrRandLoop = temp;

	} else {	  //we find the loop with smallest number of rules
		//as it will also produce smallest reason, and tend to produce smallest loop
		//formula. I.e in case of nondisj part of program it is smallest

		// now we find a loop that contains smallest
		// number of rules

		int smallestSize = -1;
		int curSize = -1;
		for (long inLoop = 0; inLoop < numSCC; inLoop++) {
			if (atomsSCC[inLoop].size() != 0) {	//if loop has no atoms then either SCC was empty
				//or its LF was sat
				curSize = rulesOfLoopsHeads[inLoop].size();
				if (smallestSize == -1)
					smallestSize = curSize;
				if (smallestSize >= curSize) {
					smallestOrRandLoop = inLoop;
				}
			}
		}
	}
	assert(smallestOrRandLoop > -1);//we assert that smallest loop is assigned to sth
	assert(atomsSCC[smallestOrRandLoop].size() > 0);
	/*
	 if(param.eloop){//if elementary loop should be found

	 //if component is HCF
	 if(!program.disj ||
	 HCFverificationSCC(atomsSCC[smallestOrRandLoop],smallestOrRandLoop)
	 ){
	 findAllEsets(elSets, atomsSCC[smallestOrRandLoop], numSCC);
	 assert(elSets.size()>0);
	 rulesOfEsets=new vector<NestedRule*>[elSets.size()];
	 int i=0;
	 for(list<vector<Atom*> >::iterator itrl=elSets.begin();
	 itrl!=elSets.end();
	 itrl++){
	 loopRulesInitSCC( (*itrl),
	 rulesOfEsets[i]);
	 i++;


	 }

	 }

	 }
	 */
	if (param.loopFormula) {		                             //assat way
		//output unsat SCC loop formulas

		if (param.loopFormula1)		//adding just one LF
			buildClausesOfLoopFormula(atomsSCC[smallestOrRandLoop],
					rulesOfLoopsHeads[smallestOrRandLoop]);
		else
			//adding all LFs
			for (long inLoop = 0; inLoop < numSCC; inLoop++) {
				if (atomsSCC[inLoop].size() != 0) {

					buildClausesOfLoopFormula(atomsSCC[inLoop],
							rulesOfLoopsHeads[inLoop]);
				}
			}
	} else {

		reasonSize = rulesOfLoopsHeads[smallestOrRandLoop].size() + 1;

		buildReasonFromLoops(atomsSCC[smallestOrRandLoop], reason,
				rulesOfLoopsHeads[smallestOrRandLoop], smallestOrRandLoop,
				modes);
		//	}

		if (reasonSize == 0) {
			cerr << endl << "Error: reasonSize is 0 ---- Error in the algoithm"
					<< endl;
			exit(24);
		}
	}
	clearInLoop(atomsSCC, numSCC);

	delete[] rulesOfLoopsHeads;
	delete[] atomsSCC;
	if (rulesOfEsets != 0)
		delete[] rulesOfEsets;
}

//at tyhe moment it find only one!
void Cmodels::findAllEsets(list<vector<Atom*> > & elSets,
		vector<Atom*> atomsSCC, long numSCC) {
	list<Atom*> elSet;
	vector<Atom*> velSet;
	int curSccId = atomsSCC[0]->inLoop;
	copyVectorToList(atomsSCC, elSet);

	//elSet will contain maximal elementary Set #1

	activeElementaryLoop(elSet, atomsSCC[0]->inLoop);
	while (elSet.size() != atomsSCC.size()) {
		//now we will try to find other maximal elementary sets
		//mark atoms in elSet with new inLoopid
		for (list<Atom*>::iterator itrEl = elSet.begin(); itrEl != elSet.end();
				itrEl++) {
			(*itrEl)->inLoop = numSCC;
		}
		copyListToVector(elSet, velSet);
		elSets.push_back(velSet);
		break;
	}
	/*
	 elSet.clear();
	 //find the rest of atoms in atomsSCC s.t. they are not in already found max loop
	 for(vector<Atom*>::iterator itrEl=atomsSCC.begin();
	 itrEl!=atomsSCC.end();
	 itrEl++){
	 if((*itrEl)->inLoop!=numSCC){
	 (*itrEl)->inLoop=curSccId;
	 elSet.push_back((*itrEl));
	 }
	 }
	 //rest of the set is found
	 if(elSet.size()==1||checkFoundnessElset(elSet, curSccId)){
	 cout<<"FOUND elSetsize atomsSCC "<<elSet.size() <<" "<<atomsSCC.size() <<endl;

	 break;
	 }
	 else{//we would like to find another maximal set
	 cout<<"UN-FOUND "<<endl;
	 copyListToVector(elSet,atomsSCC);
	 elSets.push_back(atomsSCC);
	 break;
	 //elSet will contain maximal elementary Set within atomsSCC which is now the rest
	 //	  activeElementaryLoop(elSet,atomsSCC[0]->inLoop);
	 //numSCC++;
	 }
	 }
	 */
}

void Cmodels::clearInLoop() {

	for (long indA = 0; indA < program.cmodelsAtomsFromThisId; indA++)
		program.atoms[indA]->inLoop = -1;

}
void Cmodels::clearInLoop(vector<Atom*>* atomsSCC, const long & numSCC) {
	long i;
	for (long indASCC = 0; indASCC < numSCC; indASCC++)
		for (i = 0; i < atomsSCC[indASCC].size(); i++)
			atomsSCC[indASCC][i]->inLoop = -1;

}
void Cmodels::clearInMminus() {

	for (long indA = 0; indA < program.cmodelsAtomsFromThisId; indA++)
		program.atoms[indA]->inMminus = false;

}
void Cmodels::clearInM() {

	for (long indA = 0; indA < program.cmodelsAtomsFromThisId; indA++)
		program.atoms[indA]->inM = false;

}

void Cmodels::clearInMminus(list<Atom*>& mminus) {

	for (list<Atom*>::iterator itrA = mminus.begin(); itrA != mminus.end();
			itrA++)
		(*itrA)->inMminus = false;
}
void Cmodels::clearInExp(list<Atom*>& mminus) {

	for (list<Atom*>::iterator itrA = mminus.begin(); itrA != mminus.end();
			itrA++)
		(*itrA)->exp.clear();
}
void Cmodels::clearInLoopId(list<Atom*>& mminus) {

	for (list<Atom*>::iterator itrA = mminus.begin(); itrA != mminus.end();
			itrA++)
		(*itrA)->inLoopId = -1;
}
void Cmodels::clearInAct(list<Atom*>& mminus) {

	for (list<Atom*>::iterator itrA = mminus.begin(); itrA != mminus.end();
			itrA++)
		(*itrA)->act = false;
}

bool Cmodels::HCFverification(const int & numSCC) {
	vector<Atom*>* atomsSCC = new vector<Atom*> [numSCC];
	//here we intialize the vector
	long size = program.atoms.size();
	for (long i = 0; i < size; i++)
		if (program.atoms[i]->inLoop != -1)
			atomsSCC[program.atoms[i]->inLoop].push_back(program.atoms[i]);

	bool hcf = true;
	for (long indASCC = 0; indASCC < numSCC; indASCC++) {
		if (atomsSCC[indASCC].size() > 1) { //if size of SCC is less or eq to 1 then
			//it is HCF
			hcf = HCFverificationSCC(atomsSCC[indASCC], indASCC);
			if (!hcf)
				break;
		}

	}
	delete[] atomsSCC;
	return hcf;

}
void Cmodels::markProgramsSCC(long & numSCC, bool positiveDependency) {
	list<Atom*> mminus;
	markInMminus(program.atoms);
	getMminus(mminus);
	//not with respect to model for the whole program
	enumMarkSCC(mminus, numSCC, positiveDependency, false);
	//if numSCC is 0 then program is tight
	//and we would not be within this function
	//array of vector of atoms that belong to some loop
	clearInMminus(mminus);

}
bool Cmodels::HCFverificationSCC(const vector<Atom*>&atomsSCC,
		const int& sccId) {
	long size = atomsSCC.size();
	int counter = 0;
	for (long indA = 0; indA < size; indA++) {
		if (atomsSCC[indA]->headofDR) { //if it is not then no need to go thru its
			//rules

			for (list<NestedRule*>::iterator itrNRule =
					atomsSCC[indA]->nestedRules.begin();
					itrNRule != atomsSCC[indA]->nestedRules.end(); ++itrNRule) {
				if ((*itrNRule)->sizeHead() == 1)
					break;	  //we reached part of the list where all rules are
				// nondisj and hence HCF
				else { //we are at disj rule
					   //we go thru head
					counter = 0;
					for (Atom **a = (*itrNRule)->head; a < (*itrNRule)->hend;
							a++) {
						if ((*a)->inLoop == sccId)
							counter++;
						if (counter > 1)
							return false;
					}
				}
			}
		}
	}
	return true;
}
//returns true if set is found
bool Cmodels::checkFoundnessElset(list<Atom*>& restelSet, const int& sccId) {

	for (list<Atom*>::iterator itrA = restelSet.begin();
			itrA != restelSet.end(); itrA++)
		if (!(*itrA)->found())
			return false;
	return true;

}

void Cmodels::activeElementaryLoop(list<Atom*>& elSet, const int& sccId) {
	clearInExp(elSet);
	clearInLoopId(elSet);

	list<Atom*> act;
	list<Atom*> priorityQ;
	priorityQ.clear();
	int N = elSet.size();
	list<NestedRule*>::iterator itrNRule;
	list<Atom*>::iterator itrAtom;
	assert(N > 0);
	bool satisf;
	Atom* p, *pPrime;
	Atom **a;
	while (N != 0) {
		p = elSet.front();//in place of some elements we pick first one in list
		p->inLoopId = 0;
		addPriorityQ(priorityQ, p);
		while (!priorityQ.empty()) {
			p = priorityQ.front();		  //p<-Q.rem()
			priorityQ.pop_front();
			if (p->inLoopId == 0) {
				p->inLoopId = N;
				p->root = N;
				p->exp.clear();
				act.push_front(p);
				p->act = true;
				N--;
				for (itrNRule = p->pBodyRules.begin();
						itrNRule != p->pBodyRules.end(); itrNRule++) {
					satisf = true;
					//we check if all the requierements of rule are SAT
					//B+\capSet\subseteq Act and M\sat B
					if ((*itrNRule)->bodySatisfied()) {		//then body is sat
						pPrime = p;					//p guarenteed to be in Act
						for (a = (*itrNRule)->pbody; a != (*itrNRule)->pend;
								a++) {
							if ((*a)->inLoop == sccId) {
								if (!(*a)->act) {
									satisf = false;
									break;
								} else {
									if (pPrime->inLoopId < (*a)->inLoopId) {
										pPrime = (*a);
									}
								}
							}
						}
					} else
						satisf = false;
					if (satisf) {
						for (a = (*itrNRule)->head; a != (*itrNRule)->hend;
								a++) {
							if ((*a)->inLoop == sccId)
								pPrime->exp.push_back((*a));
						}
						addPriorityQ(priorityQ, pPrime);
					}
				}

			}		  //if(p->inLoopId==0)

			if (!p->exp.empty()) {
				addPriorityQ(priorityQ, p);
				pPrime = p->exp.front();	//p.exp<-\{p`} for some p'\in p.exp
				p->exp.pop_front();
				if (pPrime->act) {
					if (p->root < pPrime->root)
						p->root = pPrime->root;
				} else if (pPrime->inLoop == sccId) {
					pPrime->inLoopId = 0;
					addPriorityQ(priorityQ, pPrime);
				}

			}		  //if(!p->exp.empty())
			else {
				if (p->inLoopId == p->root) {
					if (!priorityQ.empty() || N != 0) {
						itrAtom = elSet.begin();
						while (itrAtom != elSet.end()) {
							if ((*itrAtom)->act
									&& (*itrAtom)->inLoopId <= p->inLoopId) {
								(*itrAtom)->inLoop = -1;
								itrAtom = elSet.erase(itrAtom);
							} else
								itrAtom++;
						}
						itrAtom = act.begin();
						while (itrAtom != act.end()) {
							if ((*itrAtom)->inLoopId <= p->inLoopId) {
								(*itrAtom)->act = false;
								itrAtom = act.erase(itrAtom);
							} else
								itrAtom++;
						}
					}
				} else {
					pPrime = priorityQ.front();		  //p<-Q.rem()
					priorityQ.pop_front();
					if (pPrime->root < p->root)
						pPrime->root = p->root;
					addPriorityQ(priorityQ, pPrime);

				}

			}

		}		  //	  while(!priorityQ.empty())
	}		  //while(N!=0)
	clearInAct(act);
}
void Cmodels::addPriorityQ(list<Atom*> &Q, Atom* p) {
	if (Q.empty()) {		  //if q is empty add the element
		Q.push_front(p);
		return;
	}
	for (list<Atom*>::iterator itrQ = Q.begin(); itrQ != Q.end(); itrQ++) {
		if ((*itrQ)->id == p->id)	//elements is already in q so
			//we do not do anything
			return;
		if ((*itrQ)->inLoopId > p->inLoopId) {//insert infront of (*itrQ) and return
			Q.insert(itrQ, p);
			return;
		}
	}
}
void Cmodels::initPBodyRules() {
	Atom** a;
	list<NestedRule*>::iterator itrNRule;
	for (long indA = 0; indA < program.cmodelsAtomsFromThisId; indA++)
		for (itrNRule = program.atoms[indA]->nestedRules.begin();
				itrNRule != program.atoms[indA]->nestedRules.end();
				itrNRule++) {
			if ((*itrNRule)->sizeHead() > 1
					&& (*itrNRule)->bodyAClVerification) {
				(*itrNRule)->bodyAClVerification++;
				if ((*itrNRule)->sizeHead() == (*itrNRule)->bodyAClVerification)
					(*itrNRule)->bodyAClVerification = 0;

			} else {
				if ((*itrNRule)->sizeHead() > 1)
					(*itrNRule)->bodyAClVerification++;
				for (a = (*itrNRule)->pbody; a != (*itrNRule)->pend; a++) {

					//		  if((*a)->inLoop!=-1){//atom is in some SCC
					(*a)->addPBodyList((*itrNRule));//we do not need to creat this list
					//}
					//	for atoms that are not in any SCC
				}
			}
		}

}
void Cmodels::copyVectorToList(vector<Atom*>& from, list<Atom*>& to) {
	to.clear();
	for (int indA = 0; indA < from.size(); indA++)
		to.push_back(from[indA]);
}
void Cmodels::copyListToVector(list<Atom*>& from, vector<Atom*>& to) {
	to.clear();
	for (list<Atom*>::iterator itrA = from.begin(); itrA != from.end();
			itrA++) {
		to.push_back((*itrA));
	}
}
void Cmodels::copyVectorToList(vector<Rule*>& from, list<Rule*>& to) {
	to.clear();
	for (int indA = 0; indA < from.size(); indA++) {
		if (from[indA] != 0)
			to.push_back(from[indA]);
	}
}
void Cmodels::copyListToVector(list<Rule*>& from, vector<Rule*>& to) {
	to.clear();
	for (list<Rule*>::iterator itrA = from.begin(); itrA != from.end();
			itrA++) {
		to.push_back((*itrA));
	}
}

bool Cmodels::wellFounded() {
	Rule *rule;
	list<Rule*>::iterator itrR;
	long indA;
	Atom::change = true;

	//this while loop computes atleast
	while (Atom::change && !Atom::conflict) {
		//	program.print_atoms_wf();
		Atom::setChangeFalse();

		for (indA = 0; indA < program.atoms.size(); indA++) {

			if (program.atoms[indA]->computeFalse
					|| program.atoms[indA]->headof == 0) {
				program.atoms[indA]->setBFalse();
			}
			if (program.atoms[indA]->computeTrue0) {
				program.atoms[indA]->setComputeTrue();
			}
		}

		itrR = program.rules.begin();
		while (itrR != program.rules.end()) {
			(*itrR)->satUnsatUnknown();
			(*itrR)->propagateHeadFalse();
			(*itrR)->initUpper(); //start initialization for upper closure
			itrR++;
		}

		//here we would like to compute atmost
		//first we initialize queue program.q
		//and then we compute atmost

		for (indA = 0; indA < program.atoms.size(); indA++) {
			//the change after// introduced a bug where
			//upper closure computation was too week
			if (program.atoms[indA]->Bpos)//||program.atoms[indA]->computeTrue)

				program.q.push(program.atoms[indA]);
			program.atoms[indA]->inUpper = false;
		}
		while (!program.q.empty()) {
			Atom*a = program.q.front();

			program.q.pop();
			if (!a->inUpper && !(a->Bneg)) {
				for (itrR = a->posBodyRules.begin();
						itrR != a->posBodyRules.end(); itrR++) {
					(*itrR)->propUpper(a);

				}

				a->inUpper = true;

			}
		}
		//the atoms that are not in upper closure are in Bfalse
		for (indA = 0; indA < program.atoms.size(); indA++) {
			if (!program.atoms[indA]->inUpper)
				program.atoms[indA]->setBFalse();
		}

	}

	//erase UNSAT rules

	for (indA = 0; indA < program.atoms.size(); indA++) {
		program.atoms[indA]->posBodyRules.clear();
		program.atoms[indA]->negBodyRules.clear();
		program.atoms[indA]->headRules.clear();
	}

	return Atom::conflict;
}
bool Cmodels::completeWFM() {
	for (long indA = 0; indA < program.atoms.size(); indA++) {
		if (!program.atoms[indA]->Bpos && !program.atoms[indA]->Bneg)
			return false;
	}
	return true;
}
//implements operator PT from dlv on wellfounded model
//if PT returns true it means that PT is emptyset and that found 
//wellfounded model is an answer set
//otherwise pt returns false and we need to continue computation
bool Cmodels::pt() {

	for (list<Rule*>::iterator itrNRule = program.rules.begin();
			itrNRule != program.rules.end(); ++itrNRule) {
		if (!(*itrNRule)->pt())
			return false;
	}
	return true;
}

;
