AR = /usr/bin/ar
CC = gcc
CPP = @CPP@
CXX = g++
CXXCPP = @CXXCPP@
RANLIB = ranlib

CPPFLAGS = 
LDFLAGS = 
LIBS = 
CXXFLAGS = -g -O2
CFLAGS = -g -O2

#CC = CC
#CC = g++ 
CXXFLAGS+= -O  
#CXXFLAGS+=-g -DNEDEBUG -O  -Wno-deprecated
#CFLAGS += -g -DNEDEBUG -O  -Wno-deprecated
#CPPFLAGS += -g -DNEDEBUG -O  -Wno-deprecated

#for profiling
#CFLAGS = -g -O -pg -Wno-deprecated
#CFLAGS = -Wall -g 
#CFLAGS = -O -g -Wno-deprecated
#CFLAGS = -O3 -pg 
#CFLAGS =  -O3 -g
#CFLAGSOUT =  -O3 -g 

MFLAGS = 

ifeq (solaris, $(OSTYPE))
  MFLAGS = -D_NEED_REDEFINE_RAND_MAX_
endif

#RANLIB = ranlib
#AR = ar

.SUFFIXES: .o .cc 

HEADERS = Solver.h SimpSolver.h SolverTypes.h Vec.h Queue.h Alg.h BasicHeap.h BoxedVec.h Map.h Heap.h Sort.h \
stack.h  atomrule.h read.h graphscc.h\
 timer.h  program.h api.h ctable.h \
tree.h  cmodels.h interpret.h param.h 

SOLVER_SRCS = main.cc 
SOLVER_OBJS = $(SOLVER_SRCS:.cc=.o)

LIB_SRCS =  SimpSolver.cc Solver.cc \
	stack.cc  atomrule.cc read.cc \
timer.cc  program.cc api.cc ctable.cc \
tree.cc  graphscc.cc cmodels.cc interpret.cc 

LIB_OBJS = $(LIB_SRCS:.cc=.o)


cmodels:   $(SOLVER_OBJS) libsat.a
	  $(CXX) $(LINKFLAGS) $(CFLAGS) $(MFLAGS) $(SOLVER_OBJS) libsat.a -o ezsmtPlus

cnf_stats: cnf_stats.cc
	  $(CXX) $(LINKFLAGS) $(CFLAGS) $(MFLAGS) cnf_stats.cc -o cnf_stats

$(LIB_OBJS): $(HEADERS) Makefile


libsat.a:   $(LIB_OBJS)
	@rm -f libsat.a
	$(AR) cr libsat.a $(LIB_OBJS)
	$(RANLIB) libsat.a

#.cc.o:
#	$(CC) $(CFLAGS) $(MFLAGS) -c  $< 

clean:	
	rm -f *.o libsat.a cmodels1 cnf_stats

all: cmodels 
	 	  




