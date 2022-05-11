int: n;
int: m;
array[1..m] of int: l;
array[1..n] of int: s;
array[1..n+1, 1..n+1] of int: D;
%        d1 d2 d3 d4  O
%    d1   0  3  4  5  4
%    d2   3  0  2  6  2
%    d3   4  2  0  1  1
%    d4   5  6  1  0  2
%     O   4  2  1  2  0
%
%  D(d2, d1) = 3 ---> d2 = 2, d1 = 1
%
%   c1 0 4 2 1 0
%   c2 0 3 8 0 0
%   c3 0 5 6 7 0

array[1..m, 1..n] of var 0..1: tour;
% Puts 1 on columns which the currier has to carry
% i.e., we have 3 carries and 4 packs, this could do the tour matrix
%        d1 d2 d3 d4
%    c1   1  0  1  0   ->  c1 delivery d1 e d3
%    c2   0  1  0  0   ->  c2 delivery d2
%    c3   0  0  0  1   ->  c3 delivery d4

constraint forall(i in 1..m)(sum(j in 1..n)(tour[i, j]*s[j]) <= l[i]);
constraint forall(j in 1..n)(sum(i in 1..m)(tour[i, j]) == 1);

array[1..m, 1..n] of var 0..n: index;
index = forall(i in 1..m)(D)

var float: distance = ;
