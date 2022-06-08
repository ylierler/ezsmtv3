#include <sstream>
#include <string.h>
#include "catch2/catch_test_macros.hpp"

using std::string;

const int SUCCESS = 0;
const int FAILURE = 1;

void assertEnumeratedAnswerSetsMatchExpected(string testName) {
    string testPath = "../tests/test-programs/" + testName;
    string inputPath = testPath + ".lp";
    string expectedPath = testPath + ".expected";
    string outputPath = "temp.output";

    std::stringstream command;
    command << "./ezsmtPlus --solver-command \"../tools/cvc5 --lang smt --output-lang smt --incremental --seed 42\" " << inputPath << " -e -v 0 | sort > " << outputPath;

    int exitCode = system(command.str().c_str());
    REQUIRE(exitCode == SUCCESS);

    std::stringstream diffCommand;
    diffCommand << "diff -w " << outputPath << " " << expectedPath;

    exitCode = system(diffCommand.str().c_str());
    REQUIRE(exitCode == SUCCESS);
}

TEST_CASE("ezsmtplus enumerates all answer sets", "[integration]") {
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
}
