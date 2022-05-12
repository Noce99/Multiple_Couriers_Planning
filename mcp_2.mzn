% Use this editor as a MiniZinc scratch book
include "globals.mzn";

int: n;
int: m;
array[1..m] of int: l;
array[1..n] of int: s;
array[1..n+1, 1..n+1] of int: D;

array[1..m, 1..n] of var 0..n: tour;
%array[1..m, 1..n] of var 0..1: binary;

% Creates the binary matrix given the tour.

%constraint forall(i in 1..m, j in 1..n)(tour[i, j] > 0 -> binary[i, tour[i, j]] = 1);
%constraint forall(i in 1..m, j in 1..n)(binary[i, j] = 1 -> count_eq(row(tour, i), j, 1));

% TOUR MATRIX CONSTRAINTS

% Each sequence must contain different objects.
% After a 0 we must have all 0
constraint forall(i in 1..m, j in 1..n-1)(tour[i, j] = 0 -> tour[i, j+1] = 0);

% BINARY MATRIX CONTRAINTS

% Each object must be contained exactly once in the couriers.
% constraint forall(j in 1..n)(count_eq(col(binary, j), 1, 1));
constraint nvalue(n+1, tour);
constraint alldifferent_except_0(tour);


% Limit to the SIZE (weight) tranported by each courier.
constraint forall(i in 1..m)(sum(j in 1..n)(if tour[i, j] > 0 then s[tour[i, j]] else 0 endif) <= l[i]);

solve satisfy;

output[show(tour) ++ "\n"];
%output[show(sum(j in 1..n where binary[1, j] == 1)(s[j])) ++ "\n"];
output[show(s) ++ "\n"];
output[show(l) ++ "\n"];