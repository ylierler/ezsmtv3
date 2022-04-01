#! /bin/sh
#

#
# Runs ezcsp with clingo 5.x and uses clingo as a persistent-state solver.
# It accepts the same options as ezcsp.
# To use it, the following conditions must be satisfied:
#  1) You must be running Unix
#  2) Executable "gringo" must be in $PATH and must be a 3.x gringo
#  3) clingo-5, ezcsp, translate2 must be in $PATH
#  4) lp2aspcore2.py must be in $PATH and be executable
#  
#

MYLOC="`realpath "$0"`"
MYDIR="`dirname "$MYLOC"`"
if [ -z "$MYDIR" ]; then
	MYDIR="`pwd`"
fi

MYGRINGO="$MYDIR/pstate-gringo.sh"
MYCLASP="$MYDIR/pstate-clasp.sh"
CLINGOPY="$MYDIR/persistent-state-py.lp"

PIPEIN="/tmp/ezcsp-ps-pipe-$$.in"
PIPEOUT="/tmp/ezcsp-ps-pipe-$$.out"
mkfifo $PIPEIN
mkfifo $PIPEOUT

TMPGRINGO="/tmp/psgringo-$$"
TMPCLASP="/tmp/psclasp-$$"
TMPCLINGOPY="/tmp/pspy-$$"

sed -e 's#--PIPEIN--#'$PIPEIN'#g' -e 's#--PIPEOUT--#'$PIPEOUT'#g' "$MYGRINGO" > $TMPGRINGO
chmod a+rx $TMPGRINGO
sed -e 's#--PIPEIN--#'$PIPEIN'#g' -e 's#--PIPEOUT--#'$PIPEOUT'#g' "$MYCLASP" > $TMPCLASP
chmod a+rx $TMPCLASP
sed -e 's#--PIPEIN--#'$PIPEIN'#g' -e 's#--PIPEOUT--#'$PIPEOUT'#g' "$CLINGOPY" > $TMPCLINGOPY
chmod a+rx $TMPCLINGOPY

#echo $TMPGRINGO
#echo $TMPCLASP

clingo-5 $TMPCLINGOPY 0 -q >/dev/null 2>/dev/null &
#clingo-5 $TMPCLINGOPY 0 -q &  # DEBUG

ezcsp --skip-denials --grounder $TMPGRINGO --solver $TMPCLASP $@

rm -f $TMPGRINGO $TMPCLASP $TMPCLINGOPY
rm -f $PIPEIN $PIPEOUT
