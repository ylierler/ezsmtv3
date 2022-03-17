/*
 * File read.h 
 * Last modified on 2 19:34 2002
 * By Yuliya Babovich 
 *
 */

// Copyright 1998 by Patrik Simons
// This program is free software; you can redistribute it and/or
// modify it under the terms of the GNU General Public License
// as published by the Free Software Foundation; either version 2
// of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place - Suite 330, Boston,
// MA 02111-1307, USA.
//
// Patrik.Simons@hut.fi
#ifndef READ_H
#define READ_H

#include "rulebuilder.h"
#include <stdio.h>


class Read
{
public:
  Read (Program *p, Api *a);
  ~Read ();
  int read (string fileName);

  long models; //number of models to compute

private:
  void grow ();
  Atom* getAtom (long n);
  Atom* getAtomFromLiteral(long n);
  Atom* getFalseAtom (long n);
  int readBody (FILE *f, long size, bool pos, RuleType type);
  int finishReading(FILE* f, long size);

  void readRuleLine(istringstream&);
  void readOutputLine(istringstream& line);
  void readTheoryLine(istringstream& line);

  int addBasicRule (FILE *f);
  int addDisjunctionRule (FILE *f);
  int addConstraintRule (FILE *f);
  int addGenerateRule (FILE *f);
  int addChoiceRule (FILE *f);
  int addWeightRule (FILE *f);
  int addOptimizeRule (FILE *f);

  Atom **atoms;
  long size;
  long linenumber;
  Program * const program;
  Api * const api;
};

#endif
