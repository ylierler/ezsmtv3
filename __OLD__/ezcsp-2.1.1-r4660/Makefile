datarootdir = ${prefix}/share

srcdir = .
top_srcdir = .

prefix = /usr/local
exec_prefix = ${prefix}

bindir = ${exec_prefix}/bin
sbindir = ${exec_prefix}/sbin
libexecdir = ${exec_prefix}/libexec
datadir = ${datarootdir}
sysconfdir = ${prefix}/etc
sharedstatedir = ${prefix}/com
localstatedir = ${prefix}/var
libdir = ${exec_prefix}/lib
infodir = ${datarootdir}/info
mandir = ${datarootdir}/man
includedir = ${prefix}/include

INSTALL = /usr/bin/install -c
INSTALL_PROGRAM = ${INSTALL}
INSTALL_DATA = ${INSTALL} -m 644
INSTALL_SCRIPT = ${INSTALL}

CC = gcc
CPP = gcc -E
CXX = g++
CXXCPP = @CXXCPP@
RANLIB = @RANLIB@

WITH_CMODELS = @WITH_CMODELS@

DEFS = -DHAVE_CONFIG_H -I. -I$(srcdir) -I.. -ICMODELS/cmodels/
CPPFLAGS = 
LDFLAGS =  -LCMODELS/cmodels/ $(STATICFLAG)
LIBS = -laspparser 
CXXFLAGS = -g -O2 $(DEFS)
CFLAGS = -g -O2 $(DEFS)
RM=rm -f

LDIST = dist

CXXFLAGS += -Wall -g

LIBS += -laspparser

TRANS_PL=trans-pl
EXEC_PL=exec-pl
DORS_PL=dors-pl

CMODELS_DIR = 
#CMODELS/cmodels
CMODELS = CMODELS/cmodels/libsat.a
CMODELS_LIB = 

.PHONY: all install test-install release clean distclean


all: $(EXEC_PL).cc $(TRANS_PL).cc $(DORS_PL).cc ezcsp translate translate2 pre-parser

static:
	env STATICFLAG="-static" make all


# force the rebuild of versions.cc always
.PHONY: versions.cc
versions.cc:
	@if [ -z "`svnversion -q | grep 'Unversioned'`" -a -f tar-excluded ]; then \
		SVNREL=r`svnversion | sed -e 's/^.*://'` ; \
		echo "char *SVN_REL=(char *)\"-$$SVNREL\";" > versions.cc ;\
		echo "bool DEVELOPMENT_VER=true;" >> versions.cc ;\
	else \
		echo "char *SVN_REL=\"\";" > versions.cc ;\
		echo "bool DEVELOPMENT_VER=false;" >> versions.cc ;\
	fi

$(EXEC_PL).cc: exec.pl
	echo "char *exec_pl=(char *)" > $(EXEC_PL).cc
	./fileToC.sh exec.pl >> $(EXEC_PL).cc
	echo ";" >> $(EXEC_PL).cc

$(TRANS_PL).cc: trans.pl
	echo "char *trans_pl=(char *)" > $(TRANS_PL).cc
	./fileToC.sh trans.pl >> $(TRANS_PL).cc
	echo ";" >> $(TRANS_PL).cc

$(DORS_PL).cc: dors.pl
	echo "char *dors_pl=(char *)" > $(DORS_PL).cc
	./fileToC.sh dors.pl >> $(DORS_PL).cc
	echo ";" >> $(DORS_PL).cc

$(CMODELS):
	@if [ ! -z "$(CMODELS_DIR)" ]; then \
		cd $(CMODELS_DIR); \
		make ;\
	fi

# Rebuild whenever the library notes change
library_notes.cc: LIBRARY-NOTES.txt
	echo "char *library_notes=(char *)" > library_notes.cc
	./fileToC.sh LIBRARY-NOTES.txt >> library_notes.cc
	echo ";" >> library_notes.cc

ezcsp: $(CMODELS) ezcsp.o versions.o cmdline_params.o translate.o phpemu.o common.o pre-parser.o asp_solver.o cp_solver.o search_state.o output_model.o $(EXEC_PL).o $(TRANS_PL).o $(DORS_PL).o cp_solver_minizinc.o cp_solver_gurobi.o library_notes.o
	$(CXX) $(CXXFLAGS) $(LDFLAGS) -o ezcsp ezcsp.o versions.o cmdline_params.o translate.o phpemu.o common.o pre-parser.o asp_solver.o cp_solver.o search_state.o output_model.o $(EXEC_PL).o $(TRANS_PL).o $(DORS_PL).o cp_solver_minizinc.o cp_solver_gurobi.o library_notes.o $(LIBS) $(CMODELS_LIB)

translate: translate-main.o phpemu.o common.o cmdline_params.o search_state.o $(EXEC_PL).o $(TRANS_PL).o $(DORS_PL).o library_notes.o
	$(CXX) $(CXXFLAGS) $(LDFLAGS) -o translate translate-main.o phpemu.o common.o cmdline_params.o search_state.o $(EXEC_PL).o $(TRANS_PL).o $(DORS_PL).o library_notes.o $(LIBS)

translate-main.o: translate.cc
	$(CXX) $(CXXFLAGS) -c -o translate-main.o -DCOMPILE_TRANSLATE_MAIN translate.cc

translate2: translate2-main.o phpemu.o common.o $(EXEC_PL).o $(TRANS_PL).o $(DORS_PL).o translate2_minizinc.o translate2_gurobi.o library_notes.o TRAN/lemon
	TRAN/lemon TRAN/parser.y
	cat TRAN/parser-main >> TRAN/parser.c
	flex TRAN/lexer.l
	test -e lex.yy.c && mv lex.yy.c lexer.c
	mv lexer.c TRAN
	$(CC) $(CXXFLAGS) $(CPPFLAGS) -o TRAN/lexer.o -c TRAN/lexer.c $(LDFLAGS) $(LIBS)
	$(CXX) -I. -ITRAN $(CXXFLAGS) $(CPPFLAGS) $(LDFLAGS) -o translate2 translate2-main.o phpemu.o common.o TRAN/parser.c TRAN/lexer.o $(EXEC_PL).o $(TRANS_PL).o $(DORS_PL).o translate2_minizinc.o translate2_gurobi.o library_notes.o $(LDFLAGS) $(LIBS)

translate2-main.o: translate2.cc
	$(CXX) $(CXXFLAGS) $(CPPFLAGS)  -c -o translate2-main.o -DCOMPILE_TRANSLATE_MAIN translate2.cc  $(LDFLAGS) $(LIBS)

TRAN/lemon: TRAN/lemon.c
	# compile into host-side binary
	gcc -o TRAN/lemon TRAN/lemon.c 

pre-parser: pre-parser-main.o common.o phpemu.o
	$(CXX) $(CXXFLAGS) $(CPPFLAGS) $(LDFLAGS) -o pre-parser pre-parser-main.o common.o phpemu.o  $(LDFLAGS) $(LIBS)

pre-parser-main.o: pre-parser.cc
	$(CXX) $(CXXFLAGS) $(CPPFLAGS) -c -o pre-parser-main.o -DCOMPILE_PRE_PARSER_MAIN pre-parser.cc


test-install: ezcsp translate2
	VER=`grep "#define EZCSP_VERSION" ezcsp.cc | cut -d ' ' -f 3 | sed -e 's/"//g'` ; \
	SVNREL=r`svnversion | sed -e 's/^.*://'` ; \
	umask 22 ; mkdir -p $(bindir) ; chmod 0755 $(bindir) ; \
	$(INSTALL_PROGRAM) ezcsp $(bindir)/ezcsp-$$VER-$$SVNREL ;\
	$(INSTALL_PROGRAM) translate2 $(bindir)/translate2-$$VER-$$SVNREL

install: ezcsp translate2
	VER=`grep "#define EZCSP_VERSION" ezcsp.cc | cut -d ' ' -f 3 | sed -e 's/"//g'` ; \
	SVNREL=`svnversion | sed -e 's/^.*://'` ; \
	if [ "$$SVNREL" != "Unversioned directory" ] ; then \
		VER="$$VER-r$$SVNREL" ; \
	fi ; \
	umask 22 ; mkdir -p $(bindir) ; \
	$(RM) $(bindir)/ezcsp $(bindir)/translate2 ;\
	$(INSTALL_PROGRAM) ezcsp "$(bindir)/ezcsp-$$VER" ;\
	$(INSTALL_PROGRAM) translate2 "$(bindir)/translate2-$$VER" ;\
	ln -s "ezcsp-$$VER" $(bindir)/ezcsp ;\
	ln -s "translate2-$$VER" $(bindir)/translate2

release:
	VER=`grep "#define EZCSP_VERSION" ezcsp.cc | cut -d ' ' -f 3 | sed -e 's/"//g'` ; \
	SVNREL=r`svnversion | sed -e 's/^.*://'` ; \
	ln -s `pwd` $(LDIST)/ezcsp-$$VER-$$SVNREL ; \
	tar -C $(LDIST) -h --exclude-from tar-excluded -zcf ../ezcsp-$$VER-$$SVNREL.tgz ezcsp-$$VER-$$SVNREL ; \
	$(RM) $(LDIST)/ezcsp-$$VER-$$SVNREL


clean:
	@$(RM) *.o
	@if [ ! -z "$(CMODELS_DIR)" ]; then \
		cd $(CMODELS_DIR); make clean ; \
	fi
	@cd TRAN ; make clean
	@$(RM) ezcsp translate pre-parser

distclean: clean
	@$(RM) config.log config.status *config.cache Makefile
	@if [ ! -z "$(CMODELS_DIR)" ]; then \
		$(RM) $(CMODELS_DIR)/Makefile ; \
	fi

