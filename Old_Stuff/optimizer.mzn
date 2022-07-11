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
array[NODES, NODES] of int: D = array2d(NODES, NODES, [round(sqrt((x[i] - x[j])*(x[i] - x[j]) + (y[i] - y[j])*(y[i] - y[j]))) | i, j in NODES]);
array[COURIERS, NODES, NODES] of 0..1: table;
array[NODES, NODES, COURIERS] of var 0..1: optimized;

constraint forall(k in COURIERS, i in NODES)(sum(table[k, i, NODES]) = sum(optimized[i, NODES, k]));
constraint forall(i in NODES, k in COURIERS)(optimized[i,i,k] = 0);
constraint forall(j in NODES, k in COURIERS)(sum(optimized[NODES,j,k]) = sum(optimized[j,NODES,k]));
constraint forall(j in ITEMS)(sum(optimized[NODES, j, COURIERS]) = 1);
constraint forall(k in COURIERS)(sum(optimized[N, ITEMS, k]) = 1);

% Lento ma va
array[NODES] of var 1..n: u;
constraint u[N] = 1;
constraint forall(i in ITEMS)(u[i] >= 2);
constraint forall(i in ITEMS)(u[i] <= n);
constraint forall(k in COURIERS, i in NODES, j in 1..n)(u[i]-u[j]+1 <= (n-1)*(1-optimized[i,j,k]));




var 1..2*sum(D[N, NODES]): obj = sum(i, j in NODES, k in COURIERS)(D[i, j]*optimized[i, j, k]);
solve minimize obj;

output["["];
output[if i = 1 /\ j = 1 then "[" else "" endif ++ if j = 1 then "[" else "" endif ++ show(optimized[i, j, k]) ++ if j = N then "]," else "," endif ++ if j = N /\ i = N then "]," else "" endif | k in COURIERS, i in NODES, j in NODES];
output["]\n"];
%output[show(u) ++ "\n"];
output[show(obj) ++ "\n"];
