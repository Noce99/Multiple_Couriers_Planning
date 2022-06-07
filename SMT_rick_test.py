import numpy as np
import matplotlib.pyplot as plt
import sys
import time
import subprocess
import tempfile
from itertools import combinations
from z3 import *
import math

if len(sys.argv) < 2:
    print("Non hai messo parametri scemo!")
    quit()
try:
    istanza = int(sys.argv[1])
except:
    print("Metti un numero da 1 a 11 per runnure un'istanza, 0 per banale e -1 per banale ma non troppo!")
    quit()


file = ""
if istanza == 0:
    file = "inst_banale"
elif istanza == -1:
    file = "inst_banale_ma_non_troppo"
elif istanza < 10:
    file = "inst0{}".format(istanza)
else:
    file = "inst{}".format(istanza)
f = open('tsp_inst/' + file + ".dzn", "r")
text = f.read()
f.close()
content = text.split('\n')[:-2]
content = [content[i][4:-1] for i in range(len(content)) if content[i][0] != '%']
content[2] = content[2][1:-3]
content[3] = content[3][1:-3]
content[4] = content[4][1:-3]
content[5] = content[5][1:-3]

n = int(content[1])
m = int(content[0])

l = [int(L) for L in content[2].split(',')]
s = [int(L) for L in content[3].split(',')]
x = [int(L) for L in content[4].split(',')]
y = [int(L) for L in content[5].split(',')]

N = n + 1

D = np.array([[0 for j in range(N)] for i in range(N)])

for i in range(N):
    for j in range(N):
        D[i, j] = abs(x[i] - x[j]) + abs(y[i] - y[j])

def at_least_one(bool_vars):
    return Or(bool_vars)

def at_most_one(bool_vars):
    return [Not(And(pair[0], pair[1])) for pair in combinations(bool_vars, 2)]

def exactly_one(bool_vars):
    return at_most_one(bool_vars) + [at_least_one(bool_vars)]

def at_least_one_np(bool_vars):
    return Or(bool_vars)

def at_least_one_seq(bool_vars):
    return at_least_one_np(bool_vars)

def at_most_one_seq(bool_vars, name=""):
    constraints = []
    n = len(bool_vars)
    s = [Bool(f"s_{name}_{i}") for i in range(n - 1)]
    constraints.append(Or(Not(bool_vars[0]), s[0]))
    constraints.append(Or(Not(bool_vars[n-1]), Not(s[n-2])))
    for i in range(1, n - 1):
        constraints.append(Or(Not(bool_vars[i]), s[i]))
        constraints.append(Or(Not(bool_vars[i]), Not(s[i-1])))
        constraints.append(Or(Not(s[i-1]), s[i]))
    return And(constraints)

def exactly_one_seq(bool_vars, name=""):
    return And(at_least_one_seq(bool_vars), at_most_one_seq(bool_vars, name))



table = [[[Bool(f'table_{k}_{i}_{j}') for j in range(N)] for i in range(N)] for k in range(m)]
s = Solver()

for k in range(m):
    s.add(exactly_one_seq([table[k][N-1][j] for j in range(N)], f"primo_{k}"))

for k in range(m):
    s.add(exactly_one_seq([table[k][i][N-1] for i in range(N)], f"secondo_{k}"))

for i in range(N-1):
    s.add(exactly_one_seq([table[k][i][j] for k in range(m) for j in range(N)], f"terzo_{i}"))

for j in range(N-1):
    s.add(exactly_one_seq([table[k][i][j] for k in range(m) for i in range(N)], f"quarto_{j}"))

for k in range(m):
    for i in range(N):
        for j in range(N-1):
            s.add(Implies(table[k][i][j], exactly_one_seq([table[k][j][jj] for jj in range(N)], f"quinto_{k}_{i}_{j}")))

if s.check() == sat:
    m = s.model()
    print(m)
else:
    print("unsat")

print(s.check())
print(s.model())

"""
# Ogni corriere deve partire (xor last row)
for k in range(m):
    lines += [f"(assert (= (+ {' '.join([f'(select table {k} {N-1} {j})' for j in range(N)])}) 1))"]

# Ogni corriere deve tornare (xor last column)
for k in range(m):
    lines += [f"(assert (= (+ {' '.join([f'(select table {k} {i} {N-1})' for i in range(N)])}) 1))"]


# Un 1 per ogni riga
for i in range(N-1):
    lines += [f"(assert (= (+ {' '.join([f'(select table {k} {i} {j})' for k in range(m) for j in range(N)])}) 1))"]

# Un 1 per ogni colonna
for j in range(N-1):
    lines += [f"(assert (= (+ {' '.join([f'(select table {k} {i} {j})' for k in range(m) for i in range(N)])}) 1))"]

lines += [f"(assert (= distance (+ {' '.join([f'(* (select table {k} {i} {j}) {D[i, j]})' for k in range(m) for i in range(N) for j in range(N)])})))"]


# Edge (i, j) = 1 -> (xor in row j)
for k in range(m):
    for i in range(N):
        for j in range(N-1):
            lines += [f"(assert (or (not (select table {k} {i} {j})) (= (+ {' '.join([f'(select table {k} {j} {jj})' for jj in range(N)])}) 1)))"]

for k in range(m):
    for i in range(N-1):
        lines += [f"(assert (= (select table {k} {i} {i}) false))"]


lines += ["(check-sat)"]

for k in range(m):
    lines += [f"(get-value ({' '.join([f'(select table {k} {i} {j})' for i in range(N) for j in range(N)])}))"]

lines += ["(get-value (distance))"]

for line in lines:
    f.write(line + "\n")
f.close()
"""

quit()

for k in range(m):
    print("Tizio {}".format(k+1))
    for i in range(N):
        print(table[k][i])
    print("\n")

for i in range(N):
    for j in range(N):
        print(D[i, j]*table[0][i][j], end=" ")
    print("")

print(distancestring)
distanzacalcolatapy = 0
for k in range(m):
    for i in range(N):
        for j in range(N):
            distanzacalcolatapy += D[i, j]*table[k][i][j]

for i in range(len(x)):
    plt.gca().add_patch(plt.Circle((x[i],y[i]), 0.1, color='r'))

x1s = []
y1s = []
x2s = []
y2s = []
color_i = 1
color = 'C1'
for k in range(m):
    x1s.clear()
    y1s.clear()
    x2s.clear()
    y2s.clear()
    last = -1
    for i in range(N):
        for j in range(N):
            if table[k][i][j] > 0:
                x1s.append(x[i])
                y1s.append(y[i])
                x2s.append(x[j]-x[i])
                y2s.append(y[j]-y[i])
    plt.quiver(x1s, y1s, x2s, y2s, angles='xy', scale_units='xy', color=[color], scale=1, width=0.003)
    color_i += 1
    color = 'C'+str(color_i)
plt.xlim(min(x)-2,max(x)+2)
plt.ylim(min(y)-2,max(y)+2)
plt.show()
