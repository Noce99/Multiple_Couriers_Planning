include "globals.mzn";

predicate my_lex_lesseq_and(array[int] of var int:x, array[int] of var int:y) = 
  forall(j in 1..length(x))(
    forall(i in 1..j-1)(x[i] = y[i]) -> x[j] <= y[j]);

predicate my_lex_lesseq_or(array[int] of var int:x, array[int] of var int:y) = 
  exists(j in 1..length(x))(
    forall(i in 1..j-1)(x[i] = y[i]) /\
     if (j = length(x)) then (x[j] <= y[j]) else (x[j] < y[j]) endif);

int: n;
array[1..n] of var 1..n: q;

constraint alldifferent(q)::domain;

% Diagonal Checks
constraint alldifferent([q[i]+i | i in 1..n])::domain;
constraint alldifferent([q[i]-i | i in 1..n])::domain;

% Dual model
array[1..n, 1..n] of var bool: qb;

% Chanelling Constraint
constraint forall(i,j in 1..n)(qb[i,j] <-> q[i]=j);

% Symmetry Breaking
constraint 
my_lex_lesseq_and(array1d(qb), [qb[j,i] | i,j in 1..n]) /\  
my_lex_lesseq_and(array1d(qb), [qb[i,j] | i in reverse(1..n), j in 1..n]) /\ 
my_lex_lesseq_and(array1d(qb), [qb[j,i] | i in 1..n, j in reverse(1..n)]) /\ 
my_lex_lesseq_and(array1d(qb), [qb[i,j] | i in 1..n, j in reverse(1..n)]) /\ 
my_lex_lesseq_and(array1d(qb), [qb[j,i] | i in reverse(1..n), j in 1..n]) /\ 
my_lex_lesseq_and(array1d(qb), [qb[i,j] | i,j in reverse(1..n)]) /\
my_lex_lesseq_and(array1d(qb), [qb[j,i] | i,j in reverse(1..n)]);

solve :: int_search(q, first_fail, indomain_min) satisfy;
