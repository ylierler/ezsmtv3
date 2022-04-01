#! /bin/sh

VER=`grep "#define EZCSP_VERSION" ezcsp.cc | cut -d ' ' -f 3 | sed -e 's/"//g'`

DIR=ezcsp-$VER-win32

mkdir $DIR
mv ezcsp-$VER.exe $DIR
mv translate2-$VER.exe $DIR

zip -r ../$DIR.zip $DIR

rm -fR $DIR
