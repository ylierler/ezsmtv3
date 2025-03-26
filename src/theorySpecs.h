#ifndef THEORY_SPECS_H
#define THEORY_SPECS_H

#include <string>

std::string const LIA_THEORY = R"(
#theory lp {
    linear_term {
    - : 2, unary;
    * : 1, binary, left;
    + : 0, binary, left;
    - : 0, binary, left
    };

    dom_term {
    - : 3, unary;
    + : 3, unary;
    * : 2, binary, left;
    + : 1, binary, left;
    - : 1, binary, left;
    .. : 0, binary, left
    };

    &dom/0 : dom_term, {=}, linear_term, head;
    &sum/0 : linear_term, {<=,>=,>,<,=,!=}, linear_term, any;
    &logic/1 : linear_term, head
}.
)";

std::string const LRA_THEORY = R"(
#theory lp {
    linear_term {
    - : 2, unary;
    * : 1, binary, left;
    + : 0, binary, left;
    - : 0, binary, left
    };

    dom_term {
    - : 3, unary;
    + : 3, unary;
    * : 2, binary, left;
    + : 1, binary, left;
    - : 1, binary, left;
    .. : 0, binary, left
    };

    &dom/0 : dom_term, {=}, linear_term, head;
    &sum/0 : linear_term, {<=,>=,>,<,=,!=}, linear_term, any;
    &logic/1 : linear_term, head
}.
)";

std::string const LIRA_THEORY = R"(
#theory lp {
    linear_term {
    - : 2, unary;
    * : 1, binary, left;
    + : 0, binary, left;
    - : 0, binary, left
    };

    dom_term {
    - : 3, unary;
    + : 3, unary;
    * : 2, binary, left;
    + : 1, binary, left;
    - : 1, binary, left;
    .. : 0, binary, left
    };

    &dom/0 : dom_term, {=}, linear_term, head;
    &sum/0 : linear_term, {<=,>=,>,<,=,!=}, linear_term, any;
    &logic/1 : linear_term, head;
    &type/0 : linear_term, {=}, linear_term, head
}.
)";

std::string const IDL_THEORY = R"(
#theory lp {
    linear_term {
    - : 2, unary;
    * : 1, binary, left;
    + : 0, binary, left;
    - : 0, binary, left
    };

    dom_term {
    - : 3, unary;
    + : 3, unary;
    * : 2, binary, left;
    + : 1, binary, left;
    - : 1, binary, left;
    .. : 0, binary, left
    };

    &dom/0 : dom_term, {=}, linear_term, head;
    &diff/0 : linear_term, {<=}, linear_term, any;
    &logic/1 : linear_term, head
}.
)";

#endif