import numpy as np
import matplotlib.pyplot as plt
from ortools.sat.python import cp_model
import sys
import time

if len(sys.argv) < 2:
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

lower_boud = int(content[6][16:-1])

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
ITEMS = list(range(n))
NODES = list(range(N))
COURIERS = list(range(m))


D = np.array([[0 for j in range(N)] for i in range(N)])

for i in range(n+1):
    for j in range(n+1):
        D[i, j] = abs(x[i] - x[j]) + abs(y[i] - y[j])

model = cp_model.CpModel()

# VARIABLES
table = []
for k in COURIERS:
    rows = []
    for i in NODES:
        cols = []
        for j in NODES:
            cols.append(model.NewBoolVar(name=f't[{k},{i},{j}]'))
        rows.append(cols)
    table.append(rows)


#successor = [model.NewIntVar(0, N-1, 'successor%i' % i) for i in NODES]
#courier = [model.NewIntVar(0, N-1, 'courier%i' % i) for i in NODES]

# ------ initialization constraints ----

# Ongi oggetto raggiunto esattamente una volta
for i in ITEMS:
    model.AddExactlyOne([table[k][i][j] for k in COURIERS for j in NODES if j != i])
    model.AddExactlyOne([table[k][j][i] for k in COURIERS for j in NODES if j != i])

for k in COURIERS:
    model.Add(table[k][N-1][N-1] == 0)

# constraint forall(k in COURIERS)(sum(i in NODES, j in ITEMS)(table[i, j, k]*s[j]) <= l[k]);
for k in COURIERS:
    somma = 0
    for j in range(N-1):
        somma += sum([table[k][i][j] for i in NODES if i != j])*s[j]
    model.Add(somma <= l[k])


for k in COURIERS:
    arcs = []
    for i in NODES:
        for j in NODES:
            arcs.append((i, j, table[k][i][j]))
    model.AddCircuit(arcs)

'''
# TEST - Symmetry Breaking
for k in COURIERS:
    for j in range(N):
        for i in range(j+1, N):
            model.Add(table[k][i][n] == 0).OnlyEnforceIf(table[k][n][j])
'''

obj = cp_model.LinearExpr.Sum([table[k][i][j]*D[i, j] for k in COURIERS for i in NODES for j in NODES])
model.Add(obj >= lower_boud)

model.Minimize(obj)
solver = cp_model.CpSolver()
# Massimo 5 minuti
solver.parameters.max_time_in_seconds = 300.0
status = solver.Solve(model)


if status == cp_model.OPTIMAL or status == cp_model.FEASIBLE:
    """
    for k in COURIERS:
        print(f"\nCourier{k}:\n")
        for i in NODES:
            for j in NODES:
                print(f'{solver.Value(table[k][i][j])}', end=" ")
            print("")
        print("--------------------------------------")
    """
    print(f'Minimum of objective function: {solver.ObjectiveValue()}\n')
    for k in COURIERS:
        somma = 0
        for j in range(N-1):
            somma += sum([solver.Value(table[k][i][j]) for i in NODES if i != j])*s[j]
        print("sum[{}] = {} and l[{}] = {}".format(k, somma, k, l[k]))
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
        for i in range(N):
            for j in range(N):
                if i != j:
                    if solver.Value(table[k][i][j]) == 1:
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
else:
    print('No solution found.')

"""
plt.scatter(x[:-1], y[:-1], c='b')
for i in range(n):
    plt.annotate(f'q{i}', (x[i]+0.05, y[i]+0.05))

for k in COURIERS:
    for i in NODES:
        for j in NODES:
            if solver.Value(table[k][i][j]) == 1:
                plt.plot([x[i], x[j]], [y[i], y[j]], c='y', alpha=0.4)

plt.plot(x[-1], y[-1], c='r', marker='s')
plt.show()
"""
