include "globals.mzn";

int: n;
int: m;
array[1..m] of int: l;
array[1..n] of int: s;

%array[1..n+1] of int: x;
%array[1..n+1] of int: y;
%array[1..n+1, 1..n+1] of int: D = array2d(1..n+1, 1..n+1, [abs(x[i] - x[j]) + abs(y[i] - y[j]) | i, j in 1..n+1]);

array[1..n+1, 1..n+1] of int: D;

int: N = n+1;
int: E = N*(N-1);
array[1..E] of int: w = [D[i, j] | i in 1..N, j in 1..N where i != j];

array[1..E] of int: from = [i | i in 1..N, j in 1..N where i != j];
array[1..E] of int: to = [j | i in 1..N, j in 1..N where i != j];

array[1..N] of var bool: ns;
array[1..E] of var bool: es;

var int: dist;

constraint bounded_path(N, E, from, to, w, 1, n+1, ns, es, dist);
%constraint dpath(N, E, from, to, n+1, n+1, ns, es);
constraint bool2int(ns[7]) = 1;

solve minimize dist;


output["From: " ++ show(from[i]) ++ " To: " ++ show(to[i]) ++ " Dist: " ++ show(w[i]) ++ "\n" | i in 1..E];
output[show(ns) ++ "\n"];
output[show(es) ++ "\n"];
output[show(dist) ++ "\n"];
