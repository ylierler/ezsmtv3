#! /bin/sh
#

#if gringo gringo-test.lp; then
##if /home/marcy/SOLVERS/EZCSP/gringo-3.0.4-x86-linux/gringo gringo-test.lp; then
#	echo then-branch
#else
#	echo else-branch
#fi
GRINGO="gringo"
if ! test -z "$GRINGO" -a ! $GRINGO ./gringo-test.lp; then
   echo "The version of gringo installed at $GRINGO is known to have bugs. Please try compiling gringo from sources. To test gringo again, ensure that /path/to/gringo/gringo test-gringo.lp does not crash. gringo-test.lp can be found in the main ezcsp directory." "$LINENO" 5
fi
