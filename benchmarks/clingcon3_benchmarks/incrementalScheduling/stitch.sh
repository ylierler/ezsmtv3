#!/bin/bash

# call ./stitch.sh folder
# to put al stitched instances into this folder

folder=selected_instances
for file in ${folder}/*
do
i=$(basename "$file")
  mkdir -p $1/incrementalScheduling/clingo/
  cat encoding.clingo ${folder}/$i > $1/incrementalScheduling/clingo/$i
  mkdir -p $1/incrementalScheduling/newclingcon/
  cat encoding.casp ${folder}/$i > $1/incrementalScheduling/newclingcon/$i
  mkdir -p $1/incrementalScheduling/oldclingcon/
  cat encoding.clingcon ${folder}/$i > $1/incrementalScheduling/oldclingcon/$i
#  mkdir -p $1/incrementalScheduling/inca/
#  cat encoding.inca ${folder}/$i > $1/incrementalScheduling/inca/$i
#  mkdir -p $1/incrementalScheduling/idp/
#  cat encoding.idp aspheader.idp ${folder}/$i aspfooter.idp > $1/incrementalScheduling/idp/$i
  mkdir -p $1/incrementalScheduling/ezcsp/
  cat encoding.ezsmt ${folder}/$i > $1/incrementalScheduling/ezcsp/$i
  mkdir -p $1/incrementalScheduling/ezsmt/
  ~/work/Downloads/ezcsp-1.6.24b-r3867/ezcsp --preparse-only $1/incrementalScheduling/ezcsp/$i | gringo-3.0.5 | cmodels -cdimacs
  python ~/work/Downloads/ezsmt/code/ezcsp-dimacs-to-smt.py dimacs-completion*.out > $1/incrementalScheduling/ezsmt/$i
  rm dimacs-completion*.out
done

