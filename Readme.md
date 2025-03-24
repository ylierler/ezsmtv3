# EZSMTv3

EZSMT is a constraint answer set programming solver system that enhances the scope of Constraint Answer Set Programming (CASP) by integrating it with Satisfiability Modulo Theories (SMT) through a translational approach. It takes a program written in a Gringo 5 compatible input language, translates it into formulas written in SMT-LIB, and calls an SMT solver to compute answer sets.

EZSMT has been tested with the Z3, CVC4, CVC5, and Yices 2 SMT Solvers. However, it can interact with any SMT-LIB compatible solver that receives input from stdin. <br>
http://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/cvc4-1.8-x86_64-linux-opt <br>
https://github.com/cvc5/cvc5/releases/tag/cvc5-1.0.8 <br>
https://github.com/Z3Prover/z3/releases/tag/z3-4.8.7 <br>
https://yices.csl.sri.com/ <br>


Note: EZSMT, once built, will be able to work with 
  z3,
  cvc4,
  cvc5,
  yices-smt2
installed globally on your system and invocable under listed names; Alternatively, the executables of these systems under listed names can be placed into the tools directory.

# Quick Start
*Try the online version of EZSMT here:*

https://ezsmt.unomaha.edu/
 

# How to build EZSMT 

*The follwing installation guide specifically applies for Ubuntu. Corresponding steps can be followed for installation on Windows and MacOS.*

### Clone EZSMT repository
Clone the project and it's submodules; Note the importance of submodules with directive --recurse-submodules:

```
git clone <this-repository> --recurse-submodules
```

### Install required packages
```
apt install build-essential
```

### Download and install boost package version 1.78+ (Tested on 1.79)
Install the Boost libary, version 1.78+ from official boost website. <br>
Read more on: https://www.boost.org/doc/libs/1_79_0/more/getting_started/index.html

###### Commands for installation of version 1.79
```
wget https://archives.boost.io/release/1.79.0/source/boost_1_79_0.tar.bz2
mkdir boost
cd boost
tar --bzip2 -xf ../boost_1_79_0.tar.bz2
cd boost_1_79_0
./bootstrap.sh
./b2 install
```

### Install gringo
```
apt install gringo
```

### Install CMake
```
apt install cmake           # for ubuntu 22.04 and above
apt snap install cmake      # others
```

### Setup build pipeline using CMake

```sh
mkdir build
cd build
cmake -DCMAKE_EXPORT_COMPILE_COMMANDS=ON -DCMAKE_BUILD_TYPE=Debug ..
```

### Build the project

``` sh
# In <project_root>/build
cmake --build .
```

### Add build and tools directories to PATH
*Add build directory to your path to use EZSMT globally.* <br>
*Add tools directory to your path if you don't want to globally install them.*

``` sh
PATH="path/to/build:$PATH"
PATH="path/to/tools:$PATH"
```

### Build and test EZSMT

``` sh
# in <project_root>/build
cmake --build . && ./test
```

### Run EZSMT
```
ezsmt <encoding> <instance>
```

### Format all code

``` sh
clang-format -i src/*.cc src/*.h tests/*.cc
```
