#! /bin/sh
#

POUT="--PIPEIN--"
PIN="--PIPEOUT--"

echo "" > "$POUT"
RES="`read R < "$PIN" && echo "$R"`"
#echo "res=$RES"
cat "$RES"

rm -f "$RES"
