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

M = n + 2*m

successor = [Int(f'successor_{i}') for i in range(M)]
order = [Int(f'order_{i}') for i in range(M)]
courier = [Int(f'courier_{i}') for i in range(M)]

s = Solver()
s.add(Distinct(successor))
s.add(Distinct(order))

for i in range(M):
    s.add(successor[i] >= 0)
    s.add(successor[i] < M)
    s.add(order[i] >= 0)
    s.add(order[i] < M)

# HAMILTONIAN PATH
for i in range(M-1):
    s.add([Implies(successor[i] == j, order[j] > order[i]) for j in range(M)])

# successor[last] = first courier
s.add(successor[M-1] == n)

for i in range(n+m, M-1):
    s.add(successor[i] == i-m+1)

for i in range(n, n+m):
    s.add(courier[i] == i - n)
    s.add(courier[i+m] == i - n)

for i in range(n):
    s.add([Implies(successor[i] == j, courier[i] == courier[j]) for j in range(M) if j != i])

s.add(order[M-1] == M-1)

# DOBBIAMO AGGIUNGERE CONSTRAINTS PESO

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
