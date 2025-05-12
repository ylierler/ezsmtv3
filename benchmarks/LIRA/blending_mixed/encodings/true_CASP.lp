&dom {0..100} = q(X) :- subs(X).
&dom {0..1000} = p(X) :- subs(X).
&dom {0..20000} = c(Y,X) :- subs(X), comp(Y).

%Due to the limitation of the machine used for weighing,
%only integer amount is allowed for components.
&type {c} = int.

% Decide whether a substance is used or not.
{used(X)} :- subs(X).
&sum { q(X)} = 0 :- not used(X), subs(X).
&sum { q(X)} > 0 :- used(X), subs(X).

% Expence for each substance = quantity * cost per unit + fixed cost.
&sum {p(X)} = Z + Y*q(X) :- subs(X), cost(X,Y), used(X), using_cost(Z).
&sum { p(X)} = 0 :- subs(X), cost(X,Y), not used(X).

% Amount of each component in each substance.
&sum {c(Y,X)} = Z*q(X) :- subs(X), comp(Y), tab(X,Y,Z).

% For each component, the amount in the final product has to be
% greater than the minimum requested.
&sum {c(Y,X): subs(X)} >= Z :- comp(Y), mi(Y,Z).

% Sum of expenses cannot exceed the budget.
&sum {p(X): subs(X)}<= M :- max_money(M).

% Substances X and Y cannot be used together.
:- used(X), used(Y), not_together(X,Y).

% Requirements of minimum amount of some substances in the final product.
&sum {Z*q(X)} >= Y :- have_to_use(X,Y,Z).
