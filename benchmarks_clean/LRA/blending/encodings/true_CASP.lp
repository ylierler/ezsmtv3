&sum {q(X)}<=100 :- subs(X).
&sum {p(X)}<=1000 :- subs(X).
&sum {c(Y,X)}<=20000 :- subs(X), comp(Y).
&sum {q(X)}>=0 :- subs(X).
&sum {p(X)}>=0 :- subs(X).
&sum {c(Y,X)}>=0 :- subs(X), comp(Y).

{used(X)} :- subs(X).
&sum { q(X)}=0 :- not used(X), subs(X).
&sum { q(X)}>0 :- used(X), subs(X).

&sum {p(X); -Y * q(X)} = Z :- subs(X), cost(X,Y), used(X), using_cost(Z).
&sum { p(X)}=0  :- subs(X), cost(X,Y), not used(X).

&sum { c(Y,X); -Z*q(X) } =0 :- subs(X), comp(Y), tab(X,Y,Z).

&sum {c(Y,X):subs(X)}>= Z :- comp(Y), mi(Y,Z).

&sum {p(X):subs(X)}<= M :- max_money(M).

:- used(X), used(Y), not_together(X,Y).

&sum { Z*q(X) }>=Y :- have_to_use(X,Y,Z).
