import numpy as np
import matplotlib.pyplot as plt
import sys
import time
import subprocess
import tempfile
from itertools import combinations
from z3 import *
import math

semplification = False
if len(sys.argv) < 2:
    quit()
try:
    istanza = int(sys.argv[1])
    if len(sys.argv) > 2:
        semplification = bool(sys.argv[2]) # Vero per qualunque testo
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

lower_boud = int(content[6][16:-1])

content = [content[i][4:-1] for i in range(len(content)) if content[i][0] != '%']
content[2] = content[2][1:-3]
content[3] = content[3][1:-3]
content[4] = content[4][1:-3]
content[5] = content[5][1:-3]
content[8] = content[8][1:]
content[9] = content[9][1:]
content[10] = content[10][1:]
content[11] = content[11][1:-2]
content[12] = content[12][1:-2]

if not semplification:
    n = int(content[1])
else:
    n = int(content[7])
m = int(content[0])

l = [int(L) for L in content[2].split(',')]
if not semplification:
    s = [int(L) for L in content[3].split(',')]
    x = [int(L) for L in content[4].split(',')]
    y = [int(L) for L in content[5].split(',')]
    w = [int(L) for L in content[3].split(',')]
else:
    s = [int(L) for L in content[8].split(',')]
    all_s = [int(L) for L in content[3].split(',')]
    all_x = [int(L) for L in content[4].split(',')]
    all_y = [int(L) for L in content[5].split(',')]
    x = [float(L) for L in content[9].split(',')]
    y = [float(L) for L in content[10].split(',')]
    w = [int(L) for L in content[3].split(',')]

reconstructor_x = [L.strip()[1:-1] for L in content[11].split(';')]
reconstructor_y = [L.strip()[1:-1] for L in content[12].split(';')]
for i in range(len(reconstructor_x)):
    try:
        reconstructor_x[i] = [int(L) for L in reconstructor_x[i].split(',')]
        reconstructor_y[i] = [int(L) for L in reconstructor_y[i].split(',')]
    except:
        pass

N = n + 1

D = np.array([[0 for j in range(N)] for i in range(N)])

for i in range(N):
    for j in range(N):
        D[i, j] = abs(x[i] - x[j]) + abs(y[i] - y[j])

o = SolverFor("AUFLIRA")

obj = Int('obj')

row = []
for k in range(m):
    xxx = []
    for i in range(N):
        xxx.append(BoolVector(f'row{k}__{i}', N))
    row.append(xxx)

col = []
for k in range(m):
    yyy = []
    for i in range(N):
        yyy.append(BoolVector(f'col{k}__{i}', N))
    col.append(yyy)

order = IntVector('u', N)

for k in range(m):
    for i in range(N):
        o.add(row[k][i][i] == False)
        o.add(col[k][i][i] == False)
        for j in range(N):
            o.add(row[k][i][j] == col[k][j][i])

for k in range(m):
    for i in range(N):
        for j in range(N):
            o.add(Implies(row[k][i][j], PbEq([(x,1) for x in row[k][j]], 1)))

# print("Primi constraint: ", o.check())
# o.push()

for k in range(m):
    o.add(PbEq([(x,1) for x in row[k][N-1]], 1))
    o.add(PbEq([(x,1) for x in col[k][N-1]], 1))
    for i in range(N-1):
        o.add(PbLe([(x,1) for x in row[k][i]], 1))
        o.add(PbLe([(x,1) for x in col[k][i]], 1))

for i in range(N-1):
    o.add(PbEq([(x,1) for x in [col[k][i][j] for k in range(m) for j in range(N)]], 1))

for k in range(m):
    o.add(Sum([If(row[k][i][j], w[j], 0) for i in range(N) for j in range(N-1)]) <= l[k])

for i in range(N):
    for j in range(N-1):
        for k in range(m):
            #o.add(order[N-1] == N-1)
            o.add(order[i]-order[j]+1 <= (N-2)*(1-If(row[k][i][j], 1, 0)))

o.add(obj == Sum([If(row[k][i][j], int(D[i, j]), 0) for k in range(m) for i in range(N) for j in range(N)]))

#o.minimize(obj)

# o.set("sat.pb.solver", "solver")

if o.check() == sat:
    model = o.model()
    # print(m)
else:
    print("unsat")
    quit()

#print(s.check())
#print(s.model())


for k in range(m):
    print("Tizio {}".format(k+1))
    for i in range(N):
        for j in range(N):
            if model[row[k][i][j]]:
                print(1, end=" ")
            else:
                print(0, end=" ")
        print("")
    print("\n")

"""
for i in range(N):
    for j in range(N):
        print(D[i, j]*row[0][i][j], end=" ")
    print("")
"""

"""
print(distancestring)
distanzacalcolatapy = 0
for k in range(m):
    for i in range(N):
        for j in range(N):
            distanzacalcolatapy += D[i, j]*table[k][i][j]
"""

for i in range(len(all_x)):
    plt.gca().add_patch(plt.Circle((all_x[i],all_y[i]), 0.1, color='r'))
for i in range(len(x)):
    plt.gca().add_patch(plt.Circle((x[i],y[i]), 0.2, color='b'))

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
    for i in range(N):
        for j in range(N):
            if model[row[k][i][j]]:
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
