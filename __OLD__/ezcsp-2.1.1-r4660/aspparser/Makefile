srcdir = .
top_srcdir = .

prefix = /usr/local
exec_prefix = ${prefix}

bindir = ${exec_prefix}/bin
sbindir = ${exec_prefix}/sbin
libexecdir = ${exec_prefix}/libexec
datadir = ${prefix}/share
sysconfdir = ${prefix}/etc
sharedstatedir = ${prefix}/com
localstatedir = ${prefix}/var
libdir = ${exec_prefix}/lib
infodir = ${prefix}/share/info
mandir = ${prefix}/share/man
includedir = ${prefix}/include

INSTALL = /usr/bin/install -c
INSTALL_PROGRAM = ${INSTALL}
INSTALL_DATA = ${INSTALL} -m 644
INSTALL_SCRIPT = ${INSTALL}

AR = /usr/bin/ar
CC = gcc
CPP = @CPP@
CXX = @CXX@
CXXCPP = @CXXCPP@
RANLIB = @RANLIB@

DEFS = -DHAVE_CONFIG_H -I. -I$(srcdir) -I..
CPPFLAGS = 
LDFLAGS = 
LIBS = 
CXXFLAGS = @CXXFLAGS@ $(DEFS)
CFLAGS = -g -O2 $(DEFS)
RM=rm -f

LDIST=dist

CFLAGS += -g -Wall

PARSERLIB=libaspparser.a

.PHONY: all install clean

all: $(PARSERLIB) dlv_rsig

-include Makefile-local

$(PARSERLIB): parser.o
	$(AR) rcs $(PARSERLIB) parser.o

dlv_rsig: dlv_rsig.o parser.o
	$(CC) $(CFLAGS) -o dlv_rsig dlv_rsig.o -L. -laspparser


install: $(PARSERLIB) dlv_rsig
	@-( umask 22 ; mkdir -p $(bindir) ; chmod 0755 $(bindir) )
	@-( umask 22 ; mkdir -p $(libdir) ; chmod 0755 $(libdir) )
	@-( umask 22 ; mkdir -p $(includedir)/aspparser ; chmod 0755 $(includedir)/aspparser )
	@$(INSTALL_PROGRAM) dlv_rsig $(bindir)
	@$(INSTALL_DATA) $(PARSERLIB) $(libdir)
	@$(INSTALL_DATA) parser.h $(includedir)/aspparser


clean:
	@$(RM) *.o
	@$(RM) $(PARSERLIB) dlv_rsig

distclean: clean
	@$(RM) Makefile config.log config.status *config.cache $(PARSERLIB)
