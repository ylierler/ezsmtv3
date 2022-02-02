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

HEADERS = zchaff_base.h zchaff_clsgen.h zchaff_header.h zchaff_dbase.h zchaff_solver.h \
Solver.h SimpSolver.h SolverTypes.h Vec.h Queue.h Alg.h BasicHeap.h BoxedVec.h Map.h Heap.h Sort.h \
stack.h  atomrule.h read.h graphscc.h\
 timer.h  program.h api.h ctable.h \
tree.h  simo.h cmodels.h interpret.h param.h MiniSat_v1.12b/Solver.h  MiniSat_v1.12b/SolverTypes.h MiniSat_v1.12b/Global.h MiniSat_v1.12b/Queue.h MiniSat_v1.12b/Heap.h MiniSat_v1.12b/Sort.h MiniSat_v1.12b/VarOrder.h MiniSat_v1.12b/Constraints.h 

SOLVER_SRCS = main.cc 
SOLVER_OBJS = $(SOLVER_SRCS:.cc=.o)

LIB_SRCS =  zchaff_utils.cc \
	    zchaff_solver.cc\
	    zchaff_base.cc \
	    zchaff_dbase.cc \
	    zchaff_c_wrapper.cc \
	    zchaff_cpp_wrapper.cc \
	SimpSolver.cc Solver.cc \
	stack.cc  atomrule.cc read.cc \
timer.cc  program.cc api.cc ctable.cc \
tree.cc  simo.cc graphscc.cc cmodels.cc interpret.cc \
MiniSat_v1.12b/Solver.cc MiniSat_v1.12b/Constraints.cc

LIB_OBJS = $(LIB_SRCS:.cc=.o)


cmodels:   $(SOLVER_OBJS) libsat.a
	  $(CXX) $(LINKFLAGS) $(CFLAGS) $(MFLAGS) $(SOLVER_OBJS) libsat.a -o ezsmtPlus

zverify_bf: zverify_bf.cc	
	  $(CXX) $(LINKFLAGS) $(CFLAGS) $(MFLAGS) zverify_bf.cc -o zverify_bf

zverify_df: zverify_df.cc
	  $(CXX) $(LINKFLAGS) $(CFLAGS) $(MFLAGS) zverify_df.cc -o zverify_df

zcore: zcore_extract.cc
	  $(CXX) $(LINKFLAGS) $(CFLAGS) $(MFLAGS) zcore_extract.cc -o zcore

zminimal: zminimal.cc libsat.a
	  $(CXX) $(LINKFLAGS) $(CFLAGS) $(MFLAGS) zminimal.cc libsat.a -o zminimal

cnf_stats: cnf_stats.cc
	  $(CXX) $(LINKFLAGS) $(CFLAGS) $(MFLAGS) cnf_stats.cc -o cnf_stats

$(LIB_OBJS): $(HEADERS) Makefile

zchaff_c_wrapper.cc:	zchaff_wrapper.wrp
		sed 's/EXTERN/extern \"C\"/' zchaff_wrapper.wrp > zchaff_c_wrapper.cc

zchaff_cpp_wrapper.cc:	zchaff_wrapper.wrp
		sed 's/EXTERN//' zchaff_wrapper.wrp > zchaff_cpp_wrapper.cc

libsat.a:   $(LIB_OBJS)
	@rm -f libsat.a
	$(AR) cr libsat.a $(LIB_OBJS)
	$(RANLIB) libsat.a

#.cc.o:
#	$(CC) $(CFLAGS) $(MFLAGS) -c  $< 

clean:	
	rm -f *.o libsat.a cmodels1 *wrapper.cc zminimal zcore zverify_bf zverify_df cnf_stats

all: cmodels 
	 	  




