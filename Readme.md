# EZSMT 3

EZSMT is an constraint answer set programming solver extended from EZSMT. It takes a program written in a Gringo 5 compatible input language, translates it into formulas written in SMT-LIB, and calls an SMT solver to compute answer sets.

EZSMT has been tested with the Z3, CVC4, CVC5, and Yices 2 SMT Solvers, but it can interact with any SMT-LIB compatible solver that receives input from stdin.
http://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/cvc4-1.4-x86_64-linux-opt
https://github.com/Z3Prover/z3/releases/tag/z3-4.5.0
https://yices.csl.sri.com/

Note that EZSMT once built will be able to work with 
  z3
  cvc4
  cvc5
  yices-smt2
installed globally on your system and invocable under listed names; alternatively, the executables of these systems under listed names can be placed into tools directory (this distribution comes with executables compatible with Mac -- as of 11/22) 
 

## Quick Start

Clone the project and it's submodules; Note the importance of submodules with directive --recursive:

``` sh
git clone <this repository> --recursive
```

Install the Boost libary, version 1.78+ using your favorite package manager.
https://www.boost.org/doc/libs/1_79_0/more/getting_started/index.html

E.g., on Ubuntu 
sudo apt-get install libboost-all-dev
and on Mac
brew install boost 


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

Add ./tools to your path if you don't want to globally install them:

``` sh
# In <project_root>/build
PATH="../tools:$PATH"
```

Build, test, run:

``` sh
# In <project_root>/build
cmake --build . && ./test && ./ezsmt
```

## Format All Code

``` sh
clang-format -i src/*.cc src/*.h tests/*.cc
```
