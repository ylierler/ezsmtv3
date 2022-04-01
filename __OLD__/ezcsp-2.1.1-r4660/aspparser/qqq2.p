p(1).

p(2).

p(3).

p(4).

a(X) :-
  p(X), p(X),
  not b(X).

b(X) :-
  p(X), p(X),
  not a(X).

