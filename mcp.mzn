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
int: num_raw_combination;
array[1..num_raw_combination, 1..m] of var 0..1: raw_combination;

% Mettiamo a 0 gli elementi della matrice che siamo certi essere uguali a 0
% a causa del massimo peso portato da ogni corriere.
constraint forall(i in 1..m)(if length[i] < max_length then forall(j in (length[i]+1)..max_length)(tour[i, j] = 0)endif);

% Imponiamo che i valori non possano essere ripetuti in tour
constraint alldifferent_except_0(tour) :: domain;

% Devono comparire tutti i valori
constraint nvalue(n+1, tour) :: domain;

% Se c'è uno zero sono zero tutti quelli dopo
% testate anche voi, ma questo constraint è assolutamente inutile
constraint forall(i in 1..m, j in 1..max_length-1)(tour[i, j] = 0 -> tour[i, j+1] = 0);

% I corrieri non devono superare il peso massimo
array[1..m] of var 0..1000: occuped_l = [sum(j in 1..max_length)(if tour[i, j] != 0 then s[tour[i, j]] else 0 endif) | i in 1..m];
constraint forall(i in 1..m)(occuped_l[i] <= l[i]);

% Togliamo della simmetria (corrieri con stesso load è indifferente se si scambiano il percorso)
% constraint forall(i in 1..m, j in i+1..m where l[i] = l[j])(lex_lesseq(row(tour, i), row(tour, j)) :: domain);
constraint forall(i1 in 1..m, i2 in (i1+1)..m where l[i1] = l[i2])(lex_lesseq(array1d(tour), [if i=i1 then tour[i2, j] elseif i=i2 then tour[i1, j] else tour[i, j] endif| i in 1..m, j in 1..max_length]) :: domain);

% Togliamo simmetria loop orari e antiorari
% Noto un piccolo peggioramento delle prestazioni che è il prezzo da pagare per ridurre lo spazio di ricerca
% Se si vuole cavare basta commentare le seguenti 3 righe!
array[1..m] of var 0..max_length: not_zero_el = [sum(j in 1..max_length where tour[i, j] != 0)(1) | i in 1..m];
array[1..m, 1..max_length] of var 0..n: tour_reverse = array2d(1..m , 1..max_length, [if j <= not_zero_el[i] then tour[i, not_zero_el[i] - j + 1] else 0 endif| i in 1..m, j in 1..max_length]);
constraint forall(k in 1..num_raw_combination)(lex_lesseq(array1d(tour), [if raw_combination[k, i] = 0 then tour[i, j] else tour_reverse[i, j] endif| i in 1..m, j in 1..max_length]));

% Se un riders con più portata porta meno roba di uno che ne ha meno allora tanto vale che si scambino i percorsi
constraint forall(i in 1..m-1)(occuped_l[i] >= occuped_l[i+1]);
%constraint occuped_l[3] = 0;

% Testing !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!


%Calcoliamo la distanza totale percorsa
var 2*max(D)..2*sum(D[n+1, 1..n+1]): value;
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
