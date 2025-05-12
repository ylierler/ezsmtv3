# EZSMTv3

EZSMT is a Constraint Answer Set Programming (CASP) solver system that performs processing of logic programs with constraints using Satisfiability Modulo Theories (SMT) solving technology. 
It takes a program written in a Gringo 5 compatible input language extended with special theory atoms capable to capture constraints supported by EZSMT.
It then translates this program into formulas written in SMT-LIB, and calls an SMT solver to compute answer sets.

EZSMT has been tested with SMT Solvers CVC4, CVC5, Yices 2, and Z3. However, it can interact with any SMT-LIB compatible solver that supports input in SMT-LIB format. 

Building guide for EZSMT is [below](#How-to-build-EZSMT).


# Quick Start
For a quick start, experiment with [running EZSMT](https://ezsmt.unomaha.edu/) in your browser.


# Features
* **Linear Integer Arithmetic (LIA) constraints**
    * ```&logic(lia).```
    * ```&sum{2*x; 3*y} = 14.```
    * ```&dom{2..4; 7; 9..11} = x.```

* **Linear Real Arithmetic (LRA) constraints**
    * ```&logic(lra).```
    * ```&sum{2*x; 3*y} = "14.5".```
    * ```&dom{"2.5"..4; 7; 9..11} = x.```

* **Linear Integer Real Arithmetic (LIRA) constraints**
    * ```&logic(lira).```
    * ```&type{x; y}=int.```
    * ```&sum{2*x; 3*y; 4*z} = "18.9".```
    * ```&dom{"2.5"..4; 7; 9..11} = x.```

* **Integer Difference Logic (IDL) constraints**
    * ```&logic(idl).```
    * ```&diff{x - y} <= 7.```
    * ```&dom{2..4; 7; 9..11} = x.```

* **Optimizations**
    * ```:~ a, &sum{2*x; 3*y} = 14. [2@1]```
    * ```#minimize{-1@1:a}```
    

# Example
#### Routing Min Problem
```
% 6 nodes, start point, max cost at end node
% directed edges with cost
node(0..6).    init(0).      critical(6,7).
edge(0,1,1).   edge(1,2,4).  edge(1,4,20).   edge(1,5,3).
edge(2,3,10).  edge(2,4,2).  edge(2,5,19).   edge(3,4,6).
edge(4,5,1).   edge(4,6,2).  edge(5,6,3).

% reachtime ranges between 0 and critical value T
&dom{0..T}=at(X):- node(X), critical(Y,T).

% any edge can be in the route
{route(X,Y)} :- edge(X,Y,D).

% initial node is reached at 0.
reach(X) :- init(X).
&sum {at(X)} = 0 :- init(X).

% nodes reached later than the delay
reach(Y) :- reach(X), route(X,Y). 
&sum {at(Y); -1*at(X)} >= D :- route(X,Y), edge(X,Y,D).

% critical nodes have to be reached in time
:- critical(X,T), not reach(X).
:- critical(X,T), reach(X), &sum {at(X)}>T.

% one incoming/outgoing edge for each node
:- route(X,Y1), route(X,Y2), node(X), node(Y1), node(Y2), Y1!=Y2. 
:- route(X1,Y), route(X2,Y), node(Y), node(X1), node(X2), X1!=X2.
```

#### Benchmarks
Various Benchmark problems utilizing EZSMT can be found in this repository under benchmark subfolder

# UNO Home of the system and its documentation
The University of Nebraska Omaha home of EZSMT can be found [here](https://www.unomaha.edu/college-of-information-science-and-technology/natural-language-processing-and-knowledge-representation-lab/software/ezsmt.php). The paper documenting the system can be found there.


# How to build EZSMT
*The following building guide specifically applies for Ubuntu. Corresponding steps can be taken for building on Windows and MacOS.*

#### Clone EZSMT repository
Clone the project and it's submodules. Note the importance of submodules with directive **--recurse-submodules**.

```
git clone <this-repository> --recurse-submodules
```

#### Install required packages
Run as a root user if install command fails. (Applicable to later installs as well)
```
apt install build-essential
```


#### Download and install boost package version 1.78+ (Tested on 1.79)
Install the Boost libary, version 1.78+ from official boost website. <br>
Read more on: https://www.boost.org/doc/libs/1_79_0/more/getting_started/index.html

###### Commands for installation of version 1.79
Run final installation command as a root user to give it copy permissions.
```
wget https://archives.boost.io/release/1.79.0/source/boost_1_79_0.tar.bz2
mkdir boost
cd boost
tar --bzip2 -xf ../boost_1_79_0.tar.bz2
cd boost_1_79_0
./bootstrap.sh
./b2 install
```

#### Install gringo
```
apt install gringo
```

#### Install CMake (Version 4.0.0 or above)
```
snap install cmake --classic
```

#### Setup build pipeline using CMake

```sh
# in <project_root>
mkdir build
cd build
cmake -DCMAKE_EXPORT_COMPILE_COMMANDS=ON -DCMAKE_BUILD_TYPE=Debug -DCMAKE_POLICY_VERSION_MINIMUM=3.5 ..
```

#### Build and test EZSMT

``` sh
# in <project_root>/build
cmake --build .
./test
```

#### Add build and tools directories to PATH
*Add build directory to your path to use EZSMT globally.* <br>
*Add tools directory to your path if you don't want to globally install them.*

``` sh
PATH="path/to/build:$PATH"
PATH="path/to/tools:$PATH"
```

#### Run EZSMT
```
ezsmt <encoding> <instance> [--options]
```

Note: <br>
EZSMT, once built, will be able to work with   
  cvc4,
  cvc5,
  yices-smt2, or 
  z3
installed globally on your system and invocable under listed names; Alternatively, the executables of these systems under listed names can be placed into the tools directory. The named SMT solvers can be found at the following links:
<br>
http://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/cvc4-1.8-x86_64-linux-opt <br>
https://github.com/cvc5/cvc5/releases/tag/cvc5-1.0.8 <br>
https://github.com/Z3Prover/z3/releases/tag/z3-4.8.7 <br>
https://yices.csl.sri.com/ <br>



#### Format all code

``` sh
apt install clang-format
clang-format -i src/*.cc src/*.h src/logics/*.cc src/logics/*.h src/solver/*.cc src/solver/*.h tests/*.cc
```

# For Developers extending EZSMT with new logics

*The paper documenting the system can be found [here](https://www.unomaha.edu/college-of-information-science-and-technology/natural-language-processing-and-knowledge-representation-lab/software/ezsmt.php).* 


## Theory Specifications
The theory specifications for all currently supported logics are found in the header file [src/theorySpecs.h](/src/theorySpecs.h).
This  file can be extended to define  new theory atoms.<br>
## Reader
The [reader](/src/read.h) is used to read the ASPIF statements from the grounder Gringo 5 intermediate output. This is where the routines for newly defined theory atoms will have to be introduced.<br>
## Translation from constraint atoms syntax to SMT-LIB
The subdirectory [logics](/src/logics) has all the code that implements logics currently supported by EZSMT. This is the part that can be studied and augmented by the developer interested in extending the system with new logics/theory(constraint) atoms.


