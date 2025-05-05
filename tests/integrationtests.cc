#include <iostream>
#include <sstream>
#include <fstream>
#include <string.h>
#include <algorithm>
#include "catch2/catch_test_macros.hpp"
#include "../src/read.h"
#include "../src/logics/QF_LIA_logic.h"

using namespace std;

const int SUCCESS = 0;
const int FAILURE = 1;

string getEnumerationString(bool enumerate, int eCount, bool enumerateExtended, int eECount) {
    string enumerationString = "";
    if (enumerate) {
        enumerationString += " -e";
        if (eCount) {
            enumerationString += " " + to_string(eCount);
        }
    }
    if (enumerateExtended) {
        enumerationString += " -E";
        if (eECount) {
            enumerationString += to_string(eECount);
        }
    }
    return enumerationString;
}

string readFromFile(string filePath) {
    ifstream file(filePath);
    string content;
    if (file.is_open()) {
        string line;
        while (getline(file, line)) {
            content += line + " ";
        }
        file.close();
    }
    return content;
}

string sortCharacters(string content) {
    content.erase(std::remove(content.begin(), content.end(), ' '), content.end());
    std::sort(content.begin(), content.end());
    return content;
}

void assertEnumeratedAnswerSetsMatchExpected(string testName, bool exactComparison=true, bool enumerate=true, int eCount=0, bool enumerateExtended=true, int eECount=0, int verboseLevel=0) {
    string testPath = "../tests/test-programs/" + testName;
    string inputPath = testPath + ".lp";
    string expectedPath = testPath + ".expected";
    string outputPath = "temp.output";

    string enumerationString = getEnumerationString(enumerate, eCount, enumerateExtended, eECount);
    
    std::stringstream command;
    command << "./ezsmt --solver-command \"../tools/cvc5 --lang smt --output-lang smt --incremental --seed 42\" " << inputPath << enumerationString << " -V " << to_string(verboseLevel) << " > " << outputPath;

    cout << "Running: " << command.str() << endl;
    int exitCode = system(command.str().c_str());
    REQUIRE(exitCode == SUCCESS);
    
    if (exactComparison) {
        std::stringstream diffCommand;
        // Diff ignoring whitespace and blank lines
        diffCommand << "diff -w -B " << outputPath << " " << expectedPath;

        cout << "Running: " << diffCommand.str() << endl;
        exitCode = system(diffCommand.str().c_str());
        REQUIRE(exitCode == SUCCESS);
    }
    else {
        cout << "Sorting and comparing output content and expected content" << endl;
        string outputContent = sortCharacters(readFromFile(outputPath));
        string expectedContent = sortCharacters(readFromFile(expectedPath));
        REQUIRE(outputContent == expectedContent);
    }
}

TEST_CASE("ezsmt3 enumerates all answer sets", "[integration]") {
    SECTION("n-queens") {
        assertEnumeratedAnswerSetsMatchExpected("n-queens");
    }
    SECTION("traveling-salesperson") {
        assertEnumeratedAnswerSetsMatchExpected("traveling-salesperson");
    }
    SECTION("graph-coloring") {
        assertEnumeratedAnswerSetsMatchExpected("graph-coloring");
    }
    SECTION("empty answer set outputs blank line") {
        assertEnumeratedAnswerSetsMatchExpected("empty-answer-set");
    }
    SECTION("non-tight program should return empty answer set") {
        assertEnumeratedAnswerSetsMatchExpected("non-tight");
    }
}

TEST_CASE("Checks domain term outputs"){
    SECTION("domain term test 1") {
        assertEnumeratedAnswerSetsMatchExpected("dom-test-1", false);
    }
    SECTION("domain term test 2") {
        assertEnumeratedAnswerSetsMatchExpected("dom-test-2", false);
    }
    SECTION("domain term test 3") {
        assertEnumeratedAnswerSetsMatchExpected("dom-test-3", false);
    }
    SECTION("domain term test 4") {
        assertEnumeratedAnswerSetsMatchExpected("dom-test-4", false);
    }
}

TEST_CASE("Checks sum term outputs"){
    SECTION("sum term test 1") {
        assertEnumeratedAnswerSetsMatchExpected("sum-test-1", false);
    }
    SECTION("sum term test 2") {
        assertEnumeratedAnswerSetsMatchExpected("sum-test-2", false);
    }
    SECTION("sum term test 3") {
        assertEnumeratedAnswerSetsMatchExpected("sum-test-3", false, true, 0, false);
    }
    SECTION("sum term test real 1") {
        assertEnumeratedAnswerSetsMatchExpected("sum-test-lra-1", false, true, 0, false);
    }
    SECTION("sum term test real 2") {
        assertEnumeratedAnswerSetsMatchExpected("sum-test-lra-2", false, true, 0, false);
    }
    SECTION("sum term test real 3") {
        assertEnumeratedAnswerSetsMatchExpected("sum-test-lra-3", false, true, 0, false);
    }
    SECTION("sum term test integer real 1") {
        assertEnumeratedAnswerSetsMatchExpected("sum-test-lira-1", false, true, 0, false);
    }
}

TEST_CASE("Checks minimize directive outputs"){
    SECTION("minimize directive test 1") {
        assertEnumeratedAnswerSetsMatchExpected("minimize-test-1", false, false, 0, false);
    }
    SECTION("minimize directive test 2") {
        assertEnumeratedAnswerSetsMatchExpected("minimize-test-2", false, false, 0, false);
    }
    SECTION("minimize directive test 3") {
        assertEnumeratedAnswerSetsMatchExpected("minimize-test-3", false, false, 0, false);
    }
}
