#!/bin/bash

# call ./stitch.sh folder
# to put al stitched instances into this folder

folder=selected_instances
for file in ${folder}/*
do
i=$(basename "$file")
  mkdir -p $1/weightedTree/clingo/
  cat encoding.clingo ${folder}/$i > $1/weightedTree/clingo/$i
  mkdir -p $1/weightedTree/newclingcon/
  cat encoding.casp ${folder}/$i > $1/weightedTree/newclingcon/$i
  mkdir -p $1/weightedTree/oldclingcon/
  cat encoding.clingcon ${folder}/$i > $1/weightedTree/oldclingcon/$i
  mkdir -p $1/weightedTree/inca/
  cat encoding.inca ${folder}/$i > $1/weightedTree/inca/$i
#  mkdir -p $1/weightedTree/idp/
#  cat encoding.idp aspheader.idp ${folder}/$i aspfooter.idp > $1/weightedTree/idp/$i
  mkdir -p $1/weightedTree/ezcsp/
  cat encoding.ezcsp ${folder}/$i > $1/weightedTree/ezcsp/$i
  mkdir -p $1/weightedTree/ezsmt/
  ~/work/Downloads/ezcsp-1.6.24b-r3867/ezcsp --preparse-only $1/weightedTree/ezcsp/$i | gringo-3.0.5 | cmodels -cdimacs
  python ~/work/Downloads/ezsmt/code/ezcsp-dimacs-to-smt.py dimacs-completion*.out > $1/weightedTree/ezsmt/$i
  rm dimacs-completion*.out
done

