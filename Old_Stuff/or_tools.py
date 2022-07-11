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

x = x + [x[-1]]*(m-1)
y = y + [y[-1]]*(m-1)


N = n + m
ITEMS = list(range(n))
NODES = list(range(N))
COURIERS = list(range(m))


D = np.array([[0 for j in range(N)] for i in range(N)])

for i in range(N):
    for j in range(N):
        if i > n and j > n:
            D[i, j] = 0
        elif i > n:
            D[i, j] = abs(x[n] - x[j]) + abs(y[n] - y[j])
        elif j > n:
            D[i, j] = abs(x[i] - x[n]) + abs(y[i] - y[n])
        else:
            D[i, j] = abs(x[i] - x[j]) + abs(y[i] - y[j])

model = cp_model.CpModel()

# VARIABLES
table = []
for i in NODES:
    rows = []
    for j in NODES:
        rows.append(model.NewBoolVar(name=f't[{i},{j}]'))
    table.append(rows)


# VARIABLES
courier = []
for k in COURIERS:
    rows = []
    for i in ITEMS:
        rows.append(model.NewBoolVar(name=f'courier[{k},{i}]'))
    courier.append(rows)


# ------ initialization constraints ----

# Ongi oggetto raggiunto esattamente una volta
for i in ITEMS:
    model.AddExactlyOne(table[i][j] for j in NODES)
    model.AddExactlyOne(table[j][i] for j in NODES)

for i in ITEMS:
    model.Add(table[i][i] == False)

for i in NODES:
    for j in NODES:
        if i != j:
            model.Add(table[i][j] == False).OnlyEnforceIf(table[j][i])

for i in range(n, N):
    for j in range(n, N):
        if i != j:
            model.Add(table[i][j] == False)

for i in ITEMS:
    model.AddExactlyOne(courier[k][i] for k in COURIERS)

for i in range(n, N):
    for j in ITEMS:
        model.Add(courier[i-n][j] == True).OnlyEnforceIf(table[i][j])
        
for k in COURIERS:
    for i in ITEMS:
        for j in ITEMS:
            model.Add(courier[k][i] == courier[k][j]).OnlyEnforceIf(table[i][j])

for k in COURIERS:
    model.Add(sum(courier[k][j]*s[j] for j in ITEMS) <= l[k])

"""
# SYMMETRY BREAKING
for i in range(n, N):
    model.Add(sum(table[i][j]*(j+1)*(j+1) for j in ITEMS) >= sum(table[j][i]*(j+1)*(j+1) for j in ITEMS))   

for j in range(n, N):
    for jj in range(j+1, N):
        model.Add(sum(table[i][j]*(i+1)*(i+1) for i in ITEMS) <= sum(table[i][jj]*(i+1)*(i+1) for i in ITEMS)) 
"""

for k in COURIERS:
    for kk in range(k+1, m):
        if l[k] == l[kk]:
            model.Add(sum(courier[k][j]*(j+1)*(j+1) for j in ITEMS) <= sum(courier[kk][j]*(j+1)*(j+1) for j in ITEMS))
"""
        if l[k] >= l[kk]:
            model.Add(sum(courier[k][j]*s[j] for j in ITEMS) >= sum(courier[kk][j]*s[j] for j in ITEMS))
"""


arcs = []
for i in NODES:
    for j in NODES:
        arcs.append((i, j, table[i][j]))
model.AddCircuit(arcs)



obj = cp_model.LinearExpr.Sum([table[i][j]*D[i, j] for i in NODES for j in NODES])
model.Add(obj >= lower_boud)

model.Minimize(obj)
solver = cp_model.CpSolver()
# Massimo 5 minuti
solver.parameters.max_time_in_seconds = 300.0

solver.num_search_workers = 4
print("Start solving...")
status = solver.Solve(model)
print(status)

if status == cp_model.OPTIMAL or status == cp_model.FEASIBLE:
    
    print(f"\nPlan:\n")
    for i in NODES:
        for j in NODES:
            print(f'{solver.Value(table[i][j])}', end=" ")
        print("")
    print("--------------------------------------")

    for k in COURIERS:
        print(f"\nCourier{k}:", end=" ")
        for i in ITEMS:
            print(f'{solver.Value(courier[k][i])}', end=" ")
        

    print(f'\nMinimum of objective function: {solver.ObjectiveValue()}\n')
    for k in COURIERS:
        somma = 0
        for j in ITEMS:
            somma += solver.Value(courier[k][j])*s[j]
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
                    if solver.Value(table[i][j]):
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
