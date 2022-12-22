# EZSMT 3

EZSMT is an constraint answer set programming solver extended from EZSMT. It takes a program written in a Gringo 5 compatible input language, translates it into formulas written in SMT-LIB, and calls an SMT solver to compute answer sets.

EZSMT has been tested with the following SMT Solvers, but it can interact with any SMT-LIB compatible solver that receives input from stdin.
Z3 4.11.2
CVC4
CVC5 1.0.0
Yices 2.6.4
http://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/cvc4-1.4-x86_64-linux-opt
https://github.com/Z3Prover/z3/releases/tag/z3-4.5.0
https://yices.csl.sri.com/

## Quick Start

Clone the project and it's submodules:

```sh
git clone <this repository> --recursive
```

If you have already cloned the repository, you can use the following command to clone the submodules:

```sh
git submodule update --init --recursive
```

EZSMT expects the following dependencies to be installed on your system:

- Boost 1.7X
- Glog 0.4.0

You must install these dependencies using your system package manager. For example:

```sh
# Ubuntu
sudo apt install libboost-all-dev libgoogle-glog-dev

# Mac
brew install boost glog
```

Setup build pipeline using cmake:

```sh
mkdir build
cd build
cmake -DCMAKE_EXPORT_COMPILE_COMMANDS=ON -DCMAKE_BUILD_TYPE=Debug ..
```

Build the project in <project_root> directory:

```sh
# In <project_root>
cmake --build .
```

Optional: Add ./tools to your path if you don't want to globally install them.

```sh
# In <project_root>/build
PATH="../tools:$PATH"
```

Build, test, run:

```sh
# In <project_root>/buildPATH="../tools:$PATH"
cmake --build . && ./test && ./ezsmt
```

## Format All Code

```sh
clang-format -i src/*.cc src/*.h tests/*.cc
```
