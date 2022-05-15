% Use this editor as a MiniZinc scratch book
include "globals.mzn";

int: n;
int: m;
array[1..m] of int: l;
array[1..n] of int: s;

%array[1..n+1] of int: x;
%array[1..n+1] of int: y;
%array[1..n+1, 1..n+1] of int: D = array2d(1..n+1, 1..n+1, [abs(x[i] - x[j]) + abs(y[i] - y[j]) | i, j in 1..n+1]);

array[1..n] of int: w;
array[1..n] of int: w_acc = [sum(w[1..i]) | i in 1..n];
array[1..m] of int: length = [j-1 | i in 1..m, j in 2..n where (w_acc[j-1] < l[i] /\ w_acc[j] > l[i])];

array[1..n+1, 1..n+1] of int: D;

array[1..m, 1..n] of var 0..n: tour;
%array[1..m, 1..n+1] of var 0..max(l): freeLoad;

% TOUR MATRIX CONSTRAINTS
%constraint forall(i in 1..m)(freeLoad[i, 1] = l[i]);
%constraint forall(i in 1..m, j in 1..n)(if tour[i, j] > 0 then freeLoad[i, j+1] = freeLoad[i, j] - s[tour[i, j]] else freeLoad[i, j+1] = freeLoad[i, j] endif);

constraint forall(i in 1..m)(forall(j in length[i]+1..n)(tour[i, j] = 0));

% Each sequence must contain different objects.
constraint alldifferent_except_0(tour) :: domain;
constraint nvalue(n+1, tour) :: domain;
constraint forall(i in 1..m, j in 1..n-1)(tour[i, j] = 0 -> tour[i, j+1] = 0);

constraint forall(i in 1..m, j in i+1..m where l[i] = l[j])(lex_lesseq(row(tour, i), row(tour, j)) :: domain);

% Each object must be contained exactly once in the couriers.
%constraint forall(j in 1..n)(count_eq(tour, j, 1));

% Limit to the SIZE (weight) tranported by each courier.
constraint forall(i in 1..m)(sum(j in 1..n where tour[i, j] != 0)(s[tour[i, j]]) <= l[i]);

var 2*max(D)..2*sum(D[n+1, 1..n+1]): value;

value = sum(i in 1..m, j in 1..n-1 where tour[i, j+1] > 0)(D[tour[i, j], tour[i, j+1]]) + sum(i in 1..m, j in 1..n-1 where tour[i, j] > 0 /\ tour[i, j+1] = 0)(D[tour[i, j], n+1]) + sum(i in 1..m where tour[i, 1] > 0)(D[n+1, tour[i, 1]]);

include "Gecode.mzn";

solve 
::int_search(tour, dom_w_deg, indomain_random, complete)
::restart_luby(250)
minimize value;

output[show(tour[i, 1..n]) ++ "\n" | i in 1..m];
output[show(value)];
