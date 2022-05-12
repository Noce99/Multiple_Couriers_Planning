% Use this editor as a MiniZinc scratch book
include "globals.mzn";

int: n;
int: m;
array[1..m] of int: l;
array[1..n] of int: s;
array[1..n+1, 1..n+1] of int: D;

array[1..m, 1..n] of var 0..n: tour;
array[1..m, 1..n] of var bool: binary;

% Creates the binary matrix given the tour.
constraint forall(i in 1..m, j in 1..n)(tour[i, j] > 0 <-> binary[i, j] == 1);

% TOUR MATRIX CONSTRAINTS

% Each sequence must contain different objects.
constraint forall(i in 1..m)(alldifferent_except_0(tour[i, 1..n]));
constraint forall(i in 1..m, j in 1..n-1)(tour[i, j] == 0 -> tour[i, j+1] == 0);

% BINARY MATRIX CONTRAINTS

% Each object must be contained exactly once in the couriers.
constraint forall(j in 1..n)(exactly(1, binary[1..m, j], 1));

% Limit to the SIZE (weight) tranported by each courier.
constraint forall(i in 1..m)(sum(j in 1..n where binary[i, j] == 1)(s[j]) <= l[i]);

solve satisfy;

output[show(tour[1..m, 1..n]) ++ "\n" ++ show(binary[1..m, 1])];
output[show(sum(j in 1..n where binary[1, j] == 1)(s[j]))]

