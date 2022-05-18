# EzsmtPlus

EZSMT+ is an constraint answer set programming solver extended from EZSMT. It takes a program written in a Gringo 5 compatible input language, translates it into formulas written in SMT-LIB, and calls an SMT solver to compute answer sets.

EZSMT+ has been tested with the Z3 and CVC4 SMT Solvers, but it can interact with any SMT-LIB compatible solver that receives input from stdin.
http://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/cvc4-1.4-x86_64-linux-opt
https://github.com/Z3Prover/z3/releases/tag/z3-4.5.0

## Quick Start

Clone the project and it's submodules:

``` sh
git clone <this repository> --recursive
```

Install the Boost libary, version 1.78+ using your favorite package manager.
https://www.boost.org/doc/libs/1_79_0/more/getting_started/index.html

Setup build pipeline using cmake:

```sh
mkdir build
cd build
cmake -DCMAKE_EXPORT_COMPILE_COMMANDS=ON -DCMAKE_BUILD_TYPE=Debug ..
```

Build the project:

``` sh
# In <project_root>/build
cmake --build .
```

Feedback loop: Build, test, run:

``` sh
# In <project_root>/build
cmake --build . && ./test && ./ezsmtPlus
```

## Build For Release

```

```

## Format All Code

``` sh
clang-format -i src/*.cc src/*.h tests/*.cc
```
