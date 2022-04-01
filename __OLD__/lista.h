/*
 * File list.h 
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
#ifndef LIST_H
#define LIST_H

#include "atomrule.h"


class Node
{
public:
  Node () { next = 0; rule = 0; };

  ~Node () {};

  Node *next;  
  Node *prev;
  union {
    Rule *rule;
    Atom *atom;
    Completion *completion;   
    Clause *clause;
    bool *sol; 
  };
};

class List
{
public:
  List ();
  ~List () {};
  void pop (Node *n); 
  void push (Node *n);
  Node *head ();

private:
  Node list;
  Node *tail;
  
};

class AtomList : public List
{
public:
  AtomList () {};
  ~AtomList ();

  void push (Atom *);
  void pop (Node *);
  void deleteNode (Node *n);
};

class RuleList : public List
{
public:
  RuleList () {};
  ~RuleList ();
  
  void deleteNode (Node *n);
  void push (Rule *);  
  void pop (Node *);
};

class CompletionList : public List
{
public:

  CompletionList () {};
  ~CompletionList ();
  void deleteNode (Node *n);
  void push (Completion *);
};

class ClauseList : public List
{
public:
  ClauseList () {};
  ~ClauseList ();
  void deleteNode (Node *n);
  void push (Clause *);
};
class SolutionList : public List
{
public:
  SolutionList () {};
  ~SolutionList () ;

  void push (bool *);
};

inline Node *
List::head ()
{
  return list.next;
}

inline void
List::push (Node *n)
{
  Node * m = tail;
  n->prev = m;
  tail = n;
  m->next = tail;
}
inline void
List::pop (Node *n)
{
  if(list.next == n){
    list.next =n->next;
  
  }
  else   
    n->prev->next = n->next;
  if(n->next)
    n->next->prev = n->prev;
  else{

    tail = n->prev;
    tail->next=0;
  }
  //list.next->prev=0;
  //  delete n; 
}
inline void
AtomList::push (Atom *a)
{
  Node *n = new Node;
  n->atom = a;
  List::push (n);
}
//!!!!! pop has been changed

inline void
AtomList::pop (Node *n)
{
  List::pop (n);
  // delete n->rule;
  delete n;
  n=0;
}

inline void
AtomList::deleteNode (Node *n)
{
  List::pop (n);
  delete n->atom;
  n->atom=0;
  delete n;
  n=0;
}
inline void
RuleList::push (Rule *r)
{
  Node *n = new Node;
  n->rule = r;
  List::push (n);
}


//!!!!! pop has been changed

inline void
RuleList::pop (Node *n)
{
  List::pop (n);
  delete n->rule;
  delete n;
  n=0;
}

inline void
RuleList::deleteNode (Node *n)
{
  List::pop (n);
  delete n->rule;
  n->rule=0;
  delete n;
  n=0;
}
inline void
CompletionList::deleteNode (Node *n)
{
  List::pop (n);
  delete n->completion;
  delete n;
}

inline void
ClauseList::deleteNode (Node *n)
{
  List::pop (n);
  delete n->clause;
  delete n;
}
inline void
CompletionList::push (Completion *c)
{
  Node *n = new Node;
  n->completion = c;
  List::push (n);
}
inline void
ClauseList::push (Clause *c)
{
  Node *n = new Node;
  n->clause = c;
  List::push (n);
}
inline void
SolutionList::push (bool *c)
{
  Node *n = new Node;
  n->sol = c;
  List::push (n);
}

#endif
