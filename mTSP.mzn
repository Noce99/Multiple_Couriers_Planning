include "globals.mzn";
include "circuit.mzn";

% The number of Items
int: n;
% int: min_couriers;
int: lower_bound;
set of int: ITEMS = 1..n;

% The number of Couriers
int: m;
set of int: COURIERS = 1..m;

% The maximum Load of the Couriers
array[COURIERS] of int: l;

% The Size of each Item
array[ITEMS] of int: s;

% The Delivery Coordinates of each Item (n) + Depot (1) (last)
array[1..n+1] of int: x;
array[1..n+1] of int: y;

% The NODES in the Graph: n (ITEMS) + 2m (Depot)
int: N = n + 2*m;
set of int: NODES = 1..N;
set of int: DEPOTS = n+1..N; % last 2*m cells
set of int: START = n+1..n+m;
set of int: END = n+m+1..N;

% The Distances between Nodes
array[NODES, NODES] of int: D = array2d(NODES, NODES,
                            [if j > n /\ i > n then 0
                             else
                             (if j > n then abs(x[i] - x[n+1]) + abs(y[i] - y[n+1])
                             else
                             (if i > n then abs(x[n+1] - x[j]) + abs(y[n+1] - y[j])
                             else abs(x[i] - x[j]) + abs(y[i] - y[j]) endif) endif) endif | i, j in NODES]);

array[NODES] of var NODES: predecessor;
array[NODES] of var NODES: successor;
array[NODES] of var COURIERS: courier;

% =================================================%
% Constraints
% =================================================%

% ------ initialization constraints ---- %

% The elements of successor array must define a circuit where successor[i] = j means that j is the successor of i.
constraint circuit(successor);
constraint redundant_constraint(circuit(predecessor));

% predecessor of start nodes are end nodes
constraint redundant_constraint(
   forall(k in (n+2..n+m)) (
     predecessor[k] = k + m - 1
   )
);

constraint redundant_constraint(
   predecessor[n+1] = n+2*m
);

% successors of end nodes are start nodes
constraint redundant_constraint(
   forall(k in (n+m+1..n+m+m-1))(
     successor[k] = k - m + 1
   )
);

constraint redundant_constraint(
   successor[n+m+m] = n+1
);

constraint redundant_constraint(forall(i in NODES)(successor[predecessor[i]] = i));
constraint redundant_constraint(forall(i in NODES)(predecessor[successor[i]] = i));

% Select a Courier for each Starting and Ending point.
constraint forall(i in START)(courier[i] = i - n);   %RECALL: START = n+1..n+m;
constraint forall(i in END)(courier[i] = i - n - m); %RECALL: END = n+m+1..n+2*m;

% ------ COURIER CONSTRAINTS ---- %

% Each item is transported by the same Courier of its predecessor.
constraint forall(i in ITEMS)(courier[i] = courier[predecessor[i]]);

% Each item is transported by the same Courier of its successor.
constraint redundant_constraint(forall(i in ITEMS)(courier[i] = courier[successor[i]]));

array[COURIERS] of var int: peso = [sum(j in ITEMS where courier[j] = i)(s[j]) | i in COURIERS];
constraint forall(i in COURIERS)(peso[i] <= l[i]);

% =================================================%
% Symmetries
% =================================================%
array[NODES] of var NODES: successor_reverse = [predecessor[i] | i in NODES];
constraint forall(i in COURIERS)(lex_lesseq(successor, [if courier[j] = i then successor_reverse[j] else successor[j] endif| j in NODES]));
constraint forall(i1 in COURIERS, i2 in i1+1..m where l[i1] = l[i2])(lex_lesseq(courier, [if courier[j] = i1 then i2 elseif courier[j] = i2 then i1 else courier[j] endif| j in ITEMS]));

var 0..10000: obj = sum([(sum(j in NODES where courier[j] = i)(D[j, successor[j]])) | i in COURIERS]);

solve :: seq_search([int_search(courier, first_fail, indomain_random, complete),
int_search([successor[j] | j in NODES], dom_w_deg, indomain_random, complete)
              ])
::restart_luby(250)
minimize obj;

% =================================================%
% Output
% =================================================%

output[show(successor) ++ "\n"];
output[show(courier) ++ "\n"];
output[show(peso) ++ "\n"];
output[show(obj) ++ "\n"];

%output[forall(c in COURIERS, i in ITEMS where courier[i] = c)(show(i))];
