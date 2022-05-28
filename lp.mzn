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
%array[NODES, NODES] of int: D = array2d(NODES, NODES, [abs(x[i] - x[j]) + abs(y[i] - y[j]) | i, j in NODES]);
array[NODES, NODES] of int: D = array2d(NODES, NODES, [round(sqrt((x[i] - x[j])*(x[i] - x[j]) + (y[i] - y[j])*(y[i] - y[j]))) | i, j in NODES]);

array[NODES, NODES, COURIERS] of var 0..1: table;

constraint forall(i in NODES, k in COURIERS)(table[i,i,k] = 0);
constraint forall(j in NODES, k in COURIERS)(sum(table[NODES,j,k]) = sum(table[j,NODES,k]));
constraint forall(j in ITEMS)(sum(table[NODES, j, COURIERS]) = 1);
constraint forall(k in COURIERS)(sum(table[N, ITEMS, k]) = 1);
constraint forall(k in COURIERS)(sum(i in NODES, j in ITEMS)(table[i, j, k]*s[j]) <= l[k]);


% Esperimenti
% constraint forall(k in COURIERS, i, j in NODES where table[i, j, k] != 0)(table[j, i, k] = 0);
% constraint forall(k in COURIERS)(sum(i in NODES)(table[i, N, k]) + sum(i in NODES)(table[N, i, k]) > 0);

% array[COURIERS, NODES] of var 0..2: u = array2d(COURIERS, NODES, [sum(table[i, NODES, k])+sum(table[NODES, i, k]) | k in COURIERS, i in NODES]);
% constraint forall(k in COURIERS)(u[k, N] = 2);
% constraint forall(k in COURIERS, i in 1..n)(u[k, i] = 2 \/ u[k, i] = 0);

% Lento ma va
array[NODES] of var 1..n: u;
constraint u[N] = 1;
%constraint forall(i, j in ITEMS, k in COURIERS where table[i, j, k] != 0)(u[j] > u[i]);

% Non so se coreetto ma elimina i subtour e va un po' più veloce
constraint forall(i in ITEMS)(u[i] >= 2);
constraint forall(i in ITEMS)(u[i] <= n);
constraint forall(k in COURIERS, i in NODES, j in 1..n)(u[i]-u[j]+1 <= (n-1)*(1-table[i,j,k]));


constraint forall(k in COURIERS)(sum(table[NODES, NODES, k]) <= length[k]+1);

% Altri esperimenti
% array[NODES, NODES, COURIERS] of var 0..1: b1;
% array[NODES, NODES, COURIERS] of var 0..1: b2;
% constraint forall(i, j in ITEMS, k in COURIERS)(table[i, j, k] <= 1 - b1[i, j, k]);
% constraint forall(i, j in ITEMS, k in COURIERS)(u[j] - u[i] <= (N+1)*(1 - b2[i, j, k]));
% constraint forall(i, j in ITEMS, k in COURIERS)(b1[i, j, k] + b2[i, j, k] >= 1);


% Percorsi in senso inverso
%constraint lex_lesseq(array1d(table), [table[j, i, k] | i, j in NODES, k in COURIERS]);

%constraint forall(k1 in 1..(m-1), k2 in (k1+1)..m where l[k1] = l[k2])(lex_lesseq(array1d(table), [if k = k1 then table[i, j, k2] elseif k = k2 then table[i, j, k1] else table[i, j, k] endif| i, j in NODES, k in COURIERS]));

constraint forall(k1 in 1..(m-1), k2 in (k1+1)..m where l[k1] = l[k2])(
            (sum(i in NODES, j in ITEMS)(table[i, j, k1]*s[j]) >= sum(i in NODES, j in ITEMS)(table[i, j, k2]*s[j])));

%constraint forall(k in COURIERS)(sum(i, j in 1..n)((j-i)*table[i, j, k]) <= 0);

% Ricky matto:
% constraint u[n+1] = 0;
% constraint forall(i, j in 1..n, k in COURIERS)(table[i, j, k] + table[j, i, k] <= 1);
% constraint forall(i in NODES, j in 1..n, k in COURIERS)(table[i, j, k] = 1 -> u[j] = u[i] + 1);
% constraint forall(i in NODES, j in 1..n, k in COURIERS where table[i, j, k] = 1)(u[j] > u[i]);

var 1..2*sum(D[N, NODES]): obj = sum(i, j in NODES, k in COURIERS)(D[i, j]*table[i, j, k]);

solve minimize obj;

% output[show(table[NODES, NODES, COURIERS]) ++ "\n"];

output["["];
output[if i = 1 /\ j = 1 then "[" else "" endif ++ if j = 1 then "[" else "" endif ++ show(table[i, j, k]) ++ if j = N then "]," else "," endif ++ if j = N /\ i = N then "]," else "" endif | k in COURIERS, i in NODES, j in NODES];
output["]\n"];

% output["[|"];
% output[if i = 1 /\ j = 1 then "|" else "" endif ++ show(table[i, j, k]) ++ if j = N then "|" else "," endif | k in COURIERS, i in NODES, j in NODES];
% output["|]\n"];

%output[show(u) ++ "\n"];
output[show(obj) ++ "\n"];
