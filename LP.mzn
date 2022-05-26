include "globals.mzn";

% ITEMS
int: n;
set of int: ITEMS = 1..n;


% COURIERS
int: m;
set of int: COURIERS = 1..m;


% LOAD OF COURIERS
array[COURIERS] of int: l;
array[COURIERS] of int: length;


% SIZE OF ITEMS
array[ITEMS] of int: s;


% COORDINATES
array[1..n+1] of int: x;
array[1..n+1] of int: y;


% NODES
int: N = n + 1;
set of int: NODES = 1..N;


% DISTANCES
array[NODES, NODES] of int: D = array2d(NODES, NODES, [abs(x[i] - x[j]) + abs(y[i] - y[j]) | i, j in NODES]);


array[NODES, NODES, COURIERS] of var 0..1: table;

constraint forall(i in NODES, k in COURIERS)(table[i,i,k] = 0);
constraint forall(j in NODES, k in COURIERS)(sum(table[NODES,j,k]) = sum(table[j,NODES,k]));
constraint forall(j in 1..n)(sum(table[NODES, j, COURIERS]) = 1);
constraint forall(k in COURIERS)(sum(table[n+1, 1..n, k]) = 1);
constraint forall(k in COURIERS)(sum(i in NODES, j in 1..n)(table[i, j, k]*s[j]) <= l[k]);


% Esperimenti
% constraint forall(k in COURIERS, i, j in NODES where table[i, j, k] != 0)(table[j, i, k] = 0);
% constraint forall(k in COURIERS)(sum(i in NODES)(table[i, N, k]) + sum(i in NODES)(table[N, i, k]) > 0);

% array[COURIERS, NODES] of var 0..2: u = array2d(COURIERS, NODES, [sum(table[i, NODES, k])+sum(table[NODES, i, k]) | k in COURIERS, i in NODES]);
% constraint forall(k in COURIERS)(u[k, N] = 2);
% constraint forall(k in COURIERS, i in 1..n)(u[k, i] = 2 \/ u[k, i] = 0);

% Lento ma va
array[1..n+1] of var 0..n+1: u;
constraint forall(i, j in 1..n, k in COURIERS where table[i, j, k] != 0)(u[j] > u[i]);
% constraint u[n+1] = 0;
% constraint forall(i, j in 1..n, k in COURIERS)(table[i, j, k] + table[j, i, k] <= 1);
% constraint forall(i in NODES, j in 1..n, k in COURIERS)(table[i, j, k] = 1 -> u[j] = u[i] + 1);
% constraint forall(i in NODES, j in 1..n, k in COURIERS where table[i, j, k] = 1)(u[j] > u[i]);

var 1..10000: obj = sum(i, j in NODES, k in COURIERS)(D[i, j]*table[i, j, k]);

solve minimize obj;

% output[show(table[NODES, NODES, COURIERS]) ++ "\n"];

output["["];
output[if i = 1 /\ j = 1 then "[" else "" endif ++ if j = 1 then "[" else "" endif ++ show(table[i, j, k]) ++ if j = N then "]," else "," endif ++ if j = N /\ i = N then "]," else "" endif | k in COURIERS, i in NODES, j in NODES];
output["]\n"];
output[show(u) ++ "\n"];
output[show(obj) ++ "\n"];
