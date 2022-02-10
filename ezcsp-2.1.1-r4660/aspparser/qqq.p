a(X, Y) :-
  p(X), q(Y), o(a(X, Y)), p(X), q(Y), p(Z), q(Y),
  not b(a(X, Y)), not -a(Z, Y).

c(X) :-
  p(X), q(T),
  a(X, T).

