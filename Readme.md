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
 

## Installation and Quick Start

The follwing installtion guide is specifically for Ubuntu. Corresponding steps can be followed for installation on Windows and Mac.

### Clone EZSMT repository
Clone the project and it's submodules; Note the importance of submodules with directive --recurse-submodules:

```
git clone <this repository> --recurse-submodules
```

### Install required package
```
apt install build-essential
```

### Download and install boost package version 1.78+ (Tested on 1.79)
Install the Boost libary, version 1.78+ from official boost website. <br>
Read more on: https://www.boost.org/doc/libs/1_79_0/more/getting_started/index.html

#### Commands for installation of version 1.79:
```
wget https://archives.boost.io/release/1.79.0/source/boost_1_79_0.tar.bz2
mkdir boost
cd boost
tar --bzip2 -xf ../boost_1_79_0.tar.bz2
cd boost_1_79_0
./bootstrap.sh
./b2 ins
```

## Install gringo
```
apt install gringo
```

### Install CMake
```
apt install cmake           # for ubuntu 22.04 and above
apt snap install cmake      # others
```

### Setup build pipeline using Cmake:

```sh
mkdir build
cd build
cmake -DCMAKE_EXPORT_COMPILE_COMMANDS=ON -DCMAKE_BUILD_TYPE=Debug ..
```

### Build the project:

``` sh
# In <project_root>/build
cmake --build .
```

### Add build and tools to PATH
Add ./build to your path to use EZSMT globally. <br>
Add ./tools to your path if you don't want to globally install them.

``` sh
PATH="path/to/build:$PATH"
PATH="path/to/tools:$PATH"
```

### Build and test EZSMT:

``` sh
# In <project_root>/build
cmake --build . && ./test
```

### Run EZSMT
```
ezsmt <encoding> <instance>
```

## Format all code

``` sh
clang-format -i src/*.cc src/*.h tests/*.cc
```
