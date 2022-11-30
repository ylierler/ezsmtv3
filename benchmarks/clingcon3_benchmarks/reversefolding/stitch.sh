#!/bin/bash

# call ./stitch.sh folder
# to put al stitched instances into this folder

folder=selected_instances
for file in ${folder}/*
do
i=$(basename "$file")
  mkdir -p $1/reversefolding/clingo/
  cat encoding.clingo ${folder}/$i > $1/reversefolding/clingo/$i
  mkdir -p $1/reversefolding/newclingcon/
  cat encoding.casp ${folder}/$i > $1/reversefolding/newclingcon/$i
  mkdir -p $1/reversefolding/oldclingcon/
  cat encoding.clingcon ${folder}/$i > $1/reversefolding/oldclingcon/$i
  mkdir -p $1/reversefolding/inca/
  cat encoding.inca ${folder}/$i > $1/reversefolding/inca/$i
#  mkdir -p $1/reversefolding/idp/
#  cat encoding.idp aspheader.idp ${folder}/$i aspfooter.idp > $1/reversefolding/idp/$i
  mkdir -p $1/reversefolding/ezcsp/
  cat encoding.ezcsp ${folder}/$i > $1/reversefolding/ezcsp/$i
  mkdir -p $1/reversefolding/ezsmt/
  ~/work/Downloads/ezcsp-1.6.24b-r3867/ezcsp --preparse-only $1/reversefolding/ezcsp/$i | gringo-3.0.5 | cmodels -cdimacs
  python ~/work/Downloads/ezsmt/code/ezcsp-dimacs-to-smt.py dimacs-completion*.out > $1/reversefolding/ezsmt/$i
  rm dimacs-completion*.out
done

