#! /bin/sh

IFILE="$1"
shift

REM_IFILE="/tmp/gamstest.in"

scp "$IFILE" 172.16.210.124:$REM_IFILE
ssh 172.16.210.124 GAMS/gams24.5_linux_x64_64_sfx/gams $REM_IFILE $*
