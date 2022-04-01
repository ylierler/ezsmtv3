/*
 * File list.cc 
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
#include "lista.h"
#include "atomrule.h"
#include "program.h" //for Solution class for SolutionList

List::List ()
{
  tail = &list;
}

AtomList::~AtomList ()
{
  Node *n = head ();
  Node *t;
  while (n)
    {
      t = n->next;
	  
      if(n->atom)      
	delete n->atom;
      delete n;
      n = t;
    }
}
CompletionList::~CompletionList ()
{
   
  Node *n = head ();
  Node *t;
  while (n)
    {
      t = n->next;
      if(n->completion)
	delete n->completion;
      delete n;
      n = t;
    }
  
}
ClauseList::~ClauseList ()
{
   
  Node *n = head ();
  Node *t;
  while (n)
    {
      t = n->next;
      if(n->clause)
	delete n->clause;
      delete n;
      n = t;
    }
  
}

RuleList::~RuleList ()
{
  Node *n = head ();
  Node *t;
  while (n)
    {
      t = n->next;
      if(n->rule)      
	delete n->rule;
      delete n;
      n = t;
    }
}

SolutionList::~SolutionList ()
{
  /*
  Node *n = head ();
  Node *t;
  while (n)
    {
      t = n->next;
      if(n->sol)      
	delete n->sol;
      delete n;
      n = t;
    }
  */
}
