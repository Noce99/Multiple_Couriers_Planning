include "globals.mzn";

% The number of Items
int: n;
set of int: ITEMS = 1..n;

%int: min_couriers;
int: lower_bound;

% The number of Couriers
int: m;
set of int: COURIERS = 1..m;

% The maximum Load of the Couriers
array[COURIERS] of int: l;
array[COURIERS] of int: length;

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


array[NODES] of var NODES: successor;
array[NODES] of var COURIERS: courier;

var lower_bound..2*sum(D[N, NODES]): obj; % ?????


% =================================================%
% Constraints
% =================================================%

% ------ initialization constraints ---- %

% The elements of successor array must define a circuit where successor[i] = j means that j is the successor of i.
constraint circuit(successor);

% successors of end nodes are start nodes
constraint forall(i in n+m+1..N-1)(successor[i] = i - m + 1);

constraint successor[N] = n+1;


% Select a Courier for each Starting and Ending point.
constraint forall(i in START)(courier[i] = i - n);   %RECALL: START = n+1..n+m;fo
constraint forall(i in END)(courier[i] = i - n - m); %RECALL: END = n+m+1..n+2*m;


% ------ COURIER CONSTRAINTS ---- %

% Each item is transported by the same Courier of its successor.
constraint forall(i in ITEMS)(courier[successor[i]] = courier[i]);



% ------ LOAD CONSTRAINTS ---- %
constraint forall(i in COURIERS)(sum(j in ITEMS where courier[j] = i)(s[j]) <= l[i]);

array[COURIERS] of var int: peso;
constraint forall(i in COURIERS)(sum(j in ITEMS where courier[j] = i)(s[j]) = peso[i]);

% The max number of objects is already implied by the constraint about the maximum weight
constraint redundant_constraint(forall(i in COURIERS)(count_geq(courier, i, length[i])));

% ------ OBJECTIVE FUNCTION ---- %
%constraint obj = sum(i in NODES, j in COURIERS where courier[i] = j)(D[i, successor[i]]);
constraint obj = sum(i in NODES)(D[i, successor[i]]);

% solve :: seq_search([int_search(courier, first_fail, indomain_max, complete),
%                int_search([successor[j] | j in NODES], dom_w_deg, indomain_min, complete),
%                int_search([dist[j] | j in NODES],first_fail, indomain_min, complete),
%                int_search([load[j] | j in NODES], first_fail, indomain_min, complete)
%               ])   
% ::restart_luby(250)
% satisfy;

% solve :: seq_search([int_search(courier, first_fail, indomain_random, complete),
% int_search([successor[j] | j in NODES], dom_w_deg, indomain_random, complete)
%               ])   
% ::restart_luby(250)
% minimize obj;

solve :: seq_search([int_search(courier, first_fail, indomain_random, complete),
int_search([successor[j] | j in 1..N], dom_w_deg, indomain_random, complete)
              ])   
::restart_luby(250)
minimize obj;

% solve
% :: int_search([successor[j] | j in 1..n+m], dom_w_deg, indomain_min, complete)
% ::restart_luby(250)
% minimize obj;

%output["From: " ++ show(i) ++ " To: " ++ show(j) ++ " Dist: " ++ show(D[i, j]) ++ "\n" | i, j in 1..N];
%output[show(predecessor) ++ "\n"];
output[show(successor) ++ "\n"];
output[show(courier) ++ "\n"];
output[show(peso) ++ "\n"];
output[show(obj) ++ "\n"];

%output[if fix(courier[i]) == c then show(i) ++ "->" ++ show(successor[i]) ++ " - " else "" endif ++ if i == N then "\n" else "" endif | c in COURIERS, i in reverse(NODES)];
