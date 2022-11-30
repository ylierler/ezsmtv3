#!/bin/bash

# call ./stitch.sh folder
# to put al stitched instances into this folder

folder=instances
for file in ${folder}/*
do
i=$(basename "$file")
  mkdir -p $1/2sp/newclingcon/
  cat ${folder}/$i encoding.casp > $1/2sp/newclingcon/$i
  mkdir -p $1/2sp/oldclingcon/
  cat ${folder}/$i encoding.clingcon > $1/2sp/oldclingcon/$i
  mkdir -p $1/2sp/inca/
  cat ${folder}/$i encoding.inca > $1/2sp/inca/$i
  mkdir -p $1/2sp/aspartame/
  cat ${folder}/$i encoding.aspartame > $1/2sp/aspartame/$i
done

folder=clingoinstances
for file in ${folder}/*
do
i=$(basename "$file")
  mkdir -p $1/2sp/clingo/
  cat ${folder}/$i encoding.asp > $1/2sp/clingo/$i
done

