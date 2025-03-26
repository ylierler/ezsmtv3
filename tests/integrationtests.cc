#include <iostream>
#include <sstream>
#include <string.h>
#include "catch2/catch_test_macros.hpp"
#include "../src/read.h"
#include "../src/logics/QF_LIA_logic.h"

using std::string;
using namespace std;

const int SUCCESS = 0;
const int FAILURE = 1;

void assertEnumeratedAnswerSetsMatchExpected(string testName) {
    string testPath = "../tests/test-programs/" + testName;
    string inputPath = testPath + ".lp";
    string expectedPath = testPath + ".expected";
    string outputPath = "temp.output";

    std::stringstream command;
    command << "./ezsmt --solver-command \"../tools/cvc5 --lang smt --output-lang smt --incremental --seed 42\" " << inputPath << " -e -E -V 0 > " << outputPath;

    cout << "Running: " << command.str() << endl;
    int exitCode = system(command.str().c_str());
    REQUIRE(exitCode == SUCCESS);

    std::stringstream diffCommand;
    // Diff ignoring whitespace and blank lines
    diffCommand << "diff -w -B " << outputPath << " " << expectedPath;

    cout << "Running: " << diffCommand.str() << endl;
    exitCode = system(diffCommand.str().c_str());
    REQUIRE(exitCode == SUCCESS);
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
        assertEnumeratedAnswerSetsMatchExpected("dom-test-1");
    }
    SECTION("domain term test 2") {
        assertEnumeratedAnswerSetsMatchExpected("dom-test-2");
    }
    SECTION("domain term test 3") {
        assertEnumeratedAnswerSetsMatchExpected("dom-test-3");
    }
    SECTION("domain term test 4") {
        assertEnumeratedAnswerSetsMatchExpected("dom-test-4");
    }
}

TEST_CASE("Checks sum term outputs"){
    SECTION("sum term test 1") {
        assertEnumeratedAnswerSetsMatchExpected("sum-test-1");
    }
    SECTION("sum term test 2") {
        assertEnumeratedAnswerSetsMatchExpected("sum-test-2");
    }
}
