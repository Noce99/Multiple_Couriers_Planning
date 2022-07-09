from codecs import namereplace_errors
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
w = [int(L) for L in content[3].split(',')]
x = [int(L) for L in content[4].split(',')]
y = [int(L) for L in content[5].split(',')]

N = n + 1

D = np.array([[0 for j in range(N)] for i in range(N)])

for i in range(N):
    for j in range(N):
        D[i, j] = abs(x[i] - x[j]) + abs(y[i] - y[j])



opt = Solver()

obj = Int('obj')


table = []
for k in range(m):
    row = []
    for i in range(N):
        row.append(BoolVector(f'table{k}__{i}', N))
    table.append(row)

for k in range(m):
    for i in range(N):
        opt.add(Or([table[k][i][j] for j in range(N)]))
        opt.add(Or([table[k][j][i] for j in range(N)]))

        #opt.add(Not(table[k][i][i]))
        for j in range(N):
            for jj in range(j+1, N):
                opt.add(Not(And(table[k][i][j], table[k][i][jj])))
                opt.add(Not(And(table[k][j][i], table[k][jj][i])))





#opt.add(obj == Sum([If(row[i][j], int(D[i, j]), 0) for i in range(N) for j in range(N)]))

if opt.check() == sat:
    model = opt.model()
    # print(m)
else:
    print("unsat")
    quit()

#print(s.check())
#print(s.model())

"""
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

print("Soluzione")
for i in range(N):
    for j in range(N):
        if model[row[i][j]]:
            print(1, end=" ")
        else:
            print(0, end=" ")
    print("")
print("\n")

print("Soluzione")
for i in range(N):
    for j in range(N):
        print(model[table[i][j]], end=" ")
    print("")
print("\n")

for i in range(N):
    for j in range(N):
        print(D[i, j]*row[0][i][j], end=" ")
    print("")

quit()

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
