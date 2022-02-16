#include <ListAndSet>

p([1]).

p([1,2]).

p([1,2,3]).

a(X) v b(X) :-
  p(X), p(X).

