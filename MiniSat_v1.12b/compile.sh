# In case the Makefile doesn't work for you, try this script.

g++ -ggdb -D DEBUG -O3 Main.C Solver.C Constraints.C VarOrder.C -o minisat
