% Use this editor as a MiniZinc scratch book
include "globals.mzn";

int: n;
int: m;
int: max_length;
array[1..m] of int: l;
array[1..n] of int: s;
array[1..n] of int: w;
array[1..m] of int: length;
array[1..n+1, 1..n+1] of int: D;
array[1..m, 1..max_length] of var 0..n: tour;

% Mettiamo a 0 gli elementi della matrice che siamo certi essere uguali a 0
% a causa del massimo peso portato da ogni corriere.
constraint forall(i in 1..m)(forall(j in (length[i]+1)..max_length)(tour[i, j] = 0));

% Imponiamo che i valori non possano essere ripetuti in tour
constraint alldifferent_except_0(tour) :: domain;

% Devono comparire tutti i valori
constraint nvalue(n+1, tour) :: domain;

% Se c'è uno zero sono zero tutti quelli dopo
% testate anche voi, ma questo constraint è assolutamente inutile
% constraint forall(i in 1..m, j in 1..max_length-1)(tour[i, j] = 0 -> tour[i, j+1] = 0);

% I corrieri non devono superare il peso massimo
array[1..m] of var 0..1000: occuped_l = [sum(j in 1..max_length where tour[i, j] != 0)(s[tour[i, j]]) | i in 1..m];
constraint forall(i in 1..m)(occuped_l[i] <= l[i]);

% Togliamo della simmetria (corrieri identici)
constraint forall(i in 1..m, j in i+1..m where l[i] = l[j])(lex_lesseq(row(tour, i), row(tour, j)) :: domain);

% Togliamo simmetria loop orari e antiorari
% Noto un piccolo peggioramento delle prestazioni che è il prezzo da pagare per ridurre lo spazio di ricerca
% Se si vuole cavare basta commentare le seguenti 3 righe!
array[1..m] of var 0..max_length: not_zero_el = [sum(j in 1..max_length where tour[i, j] != 0)(1) | i in 1..m];
array[1..m, 1..max_length] of var 0..n: tour_reverse = array2d(1..m , 1..max_length, [if j <= not_zero_el[i] then tour[i, not_zero_el[i] - j + 1] else 0 endif| i in 1..m, j in 1..max_length]);
constraint forall(i in 1..m)(lex_lesseq(row(tour, i), row(tour_reverse, i)));

% Testing !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
%constraint forall(i in 1..m-1)(occuped_l[i] >= occuped_l[i+1]);

var 2*max(D)..2*sum(D[n+1, 1..n+1]): value;
%Calcoliamo la distanza totale percorsa
value = sum(i in 1..m, j in 1..max_length-1 where tour[i, j+1] > 0)(D[tour[i, j], tour[i, j+1]]) + sum(i in 1..m, j in 1..max_length-1 where tour[i, j] > 0 /\ tour[i, j+1] = 0)(D[tour[i, j], n+1]) + sum(i in 1..m where tour[i, max_length] > 0)(D[tour[i, max_length], n+1]) + sum(i in 1..m where tour[i, 1] > 0)(D[n+1, tour[i, 1]]);

solve 
::int_search(tour, dom_w_deg, indomain_random, complete)
::restart_luby(250)
minimize value;

output["Tour: \n"];
output[show(tour[i, 1..max_length]) ++ "\n" | i in 1..m];
%output["Reverse Tour: \n"];
%output[show(tour_reverse[i, 1..max_length]) ++ "\n" | i in 1..m];
output["Occuped_l:\n"];
output[show(occuped_l) ++ "\n"];
output[show(value) ++ "\n"];
