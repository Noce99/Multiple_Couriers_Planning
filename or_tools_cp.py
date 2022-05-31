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

N = n + 2*m
ITEMS = list(range(n))
NODES = list(range(N))
COURIERS = list(range(m))
START = list(range(n, n+m))
END = list(range(n+m, N))

D = np.array([[0 for j in range(n+1)] for i in range(n+1)])

for i in range(n+1):
    for j in range(n+1):
        D[i, j] = abs(x[i] - x[j]) + abs(y[i] - y[j])



model = cp_model.CpModel()

successor = []
courier = []

for i in NODES:
    successor.append(model.NewIntVar(0, N-1, f'successor[{i}]'))

for i in NODES:
    courier.append(model.NewIntVar(0, m-1, f'courier[{i}]'))

#successor = [model.NewIntVar(0, N-1, 'successor%i' % i) for i in NODES]
#courier = [model.NewIntVar(0, N-1, 'courier%i' % i) for i in NODES]

# ------ initialization constraints ----

for i in NODES:
    model.AddCircuit((i, successor[i], 1))

for i in range(n+m+1, N-1):
    model.AddElement(i, successor, i-m+1)

model.Add(successor[N] == n+1)

for i in START:
    model.Add(courier[i] == i - n)
for i in END:
    model.Add(courier[i] == i - n - m)

# ------ COURIER CONSTRAINTS ----
for i in ITEMS:
    model.Add(courier[successor[i]] == courier[i])

# ------ LOAD CONSTRAINTS ----
for i in COURIERS:
    model.Add(np.sum(s[j] for j in ITEMS if courier[j] == i) <= l[i])

# ------ OBJECTIVE FUNCTION ---- %
obj = np.sum(D[i, successor[i]] for i in NODES)

solver.Minimize(obj)

solver = cp_model.CpSolver()
status = solver.Solve(model)

if status == cp_model.OPTIMAL or status == cp_model.FEASIBLE:
    print(f'Minimum of objective function: {solver.ObjectiveValue()}\n')
    print(f'successor = {solver.Value(successor)}')
else:
    print('No solution found.')
