% Use this editor as a MiniZinc scratch book
include "globals.mzn";

int: n;
int: m;
array[1..m] of int: l;
array[1..n] of int: s;
array[1..n+1, 1..n+1] of int: D;

array[1..m, 1..n] of var 0..n: tour;
%array[1..m, 1..n+1] of var 0..max(l): freeLoad;

% TOUR MATRIX CONSTRAINTS
%constraint forall(i in 1..m)(freeLoad[i, 1] = l[i]);
%constraint forall(i in 1..m, j in 1..n)(if tour[i, j] > 0 then freeLoad[i, j+1] = freeLoad[i, j] - s[tour[i, j]] else freeLoad[i, j+1] = freeLoad[i, j] endif);

% Each sequence must contain different objects.
constraint alldifferent_except_0(tour);
constraint nvalue(n+1, tour);
constraint forall(i in 1..m, j in 1..n-1)(tour[i, j] = 0 -> tour[i, j+1] = 0);

% Each object must be contained exactly once in the couriers.
%constraint forall(j in 1..n)(count_eq(tour, j, 1));

% Limit to the SIZE (weight) tranported by each courier.
constraint forall(i in 1..m)(sum(j in 1..n where tour[i, j] != 0)(s[tour[i, j]]) <= l[i]);

include "Gecode.mzn";

solve 
::int_search(tour, dom_w_deg, indomain_random)
::restart_luby(250)
satisfy;

output[show(tour[1..m, 1..n])];
%output[show(freeLoad)];
