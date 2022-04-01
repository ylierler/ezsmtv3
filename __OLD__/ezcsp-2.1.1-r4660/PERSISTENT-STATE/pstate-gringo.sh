#! /bin/sh
#

# Whether input is in ASPCORE2 or not
ASPCORE2_INPUT=0

POUT="--PIPEIN--"
PIN="--PIPEOUT--"


TFILE=/tmp/pstate-gringo-input-$$

if [ "$ASPCORE2_INPUT" = "1" ]; then
	if [ $# = 1 ]; then
		ASPFILE="$1"
		TFILE=""
	else
		cat $@ > "$TFILE"
		ASPFILE="$TFILE"
	fi
else
	gringo $@ | lp2aspcore2.py > "$TFILE"
	ASPFILE="$TFILE"
fi

echo "$ASPFILE" > "$POUT"
RES="`read R < "$PIN" && echo "$R"`"
#echo "res=$RES"

if [ ! -z "$TFILE" ]; then
	rm -f "$TFILE"
fi
