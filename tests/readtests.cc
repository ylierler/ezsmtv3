#include "read.h"
#include "program.h"
#include "rulebuilder.h"
#include <catch2/catch_test_macros.hpp>

TEST_CASE("", "")
{
    Program* program = new Program();
    Api* api = new Api(program);
    Read read (program, api);



    REQUIRE(true);
}
