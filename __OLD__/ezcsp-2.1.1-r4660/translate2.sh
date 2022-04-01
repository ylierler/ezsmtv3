#! /bin/sh
#

echo "$*" > /tmp/wwwxxx
cp "$2" "/tmp/wwwxxx.in"
./translate2 $*
