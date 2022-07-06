import numpy as np
import gurobipy as gp
from gurobipy import quicksum
from gurobipy import GRB
import scipy.sparse as sp
import matplotlib.pyplot as plt
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

D = np.array([[0 for j in range(N)] for i in range(N)])

for i in range(N):
    for j in range(N):
        D[i, j] = abs(x[i] - x[j]) + abs(y[i] - y[j])

gp.setParam("PoolSearchMode", 2) # Cerca meglio le soluzioni intermedie
gp.setParam("TimeLimit", 300)# Dopo 5 minuti si ferma e mostra il meglio che ha ottenuto
try:
    model = gp.Model("MCP")
    table = model.addMVar(shape=(m, N, N), vtype=GRB.BINARY, name="table")
    u = model.addMVar(shape=(N), lb=1, ub=N, vtype=GRB.INTEGER, name="u")

    obj = quicksum(D[i, j]*table[k, i, j] for i in range(N) for j in range(N) for k in range(m))
    model.addConstr(obj >= lower_boud)
    model.setObjective(obj, GRB.MINIMIZE)

    for i in range(N):
        for k in range(m):
            model.addConstr(table[k,i,i] == 0)
            model.addConstr(quicksum(table[k,i,j] for j in range(N)) == quicksum(table[k,j,i] for j in range(N)))

    for j in range(N-1):
        model.addConstr(quicksum(table[k, i, j] for k in range(m) for i in range(N)) == 1)

    for k in range(m):
        model.addConstr(quicksum(table[k, N-1, j] for j in range(N-1)) == 1)
        model.addConstr(quicksum(table[k, j, N-1] for j in range(N-1)) == 1)
        model.addConstr(quicksum(table[k, i, j]*s[j] for i in range(N) for j in range(N-1)) <= l[k])

    for i in range(N):
        for j in range(N-1):
            for k in range(m):
                # Nuovo di Riky
                model.addConstr(u[N-1] == 1)
                #model.addConstr(u[i]-u[j]+1 <= (N-2)*(1-table[k, i, j]))
                # Vecchio di Noce:
                model.addConstr(table[k, i, j]*u[j] >= table[k, i, j]*(u[i]+1))
    """
    # Add row and column constraints
    for i in range(n):

        # At most one queen per row
        m.addConstr(x[i, :].sum() <= 1, name="row"+str(i))

        # At most one queen per column
        m.addConstr(x[:, i].sum() <= 1, name="col"+str(i))

    # Add diagonal constraints
    for i in range(1, 2*n):

        # At most one queen per diagonal
        diagn = (range(max(0, i-n), min(n, i)), range(min(n, i)-1, max(0, i-n)-1, -1))
        m.addConstr(x[diagn].sum() <= 1, name="diag"+str(i))

        # At most one queen per anti-diagonal
        adiagn = (range(max(0, i-n), min(n, i)), range(max(0, n-i), min(n, 2*n-i)))
        m.addConstr(x[adiagn].sum() <= 1, name="adiag"+str(i))
    """
    # Optimize model
    model.optimize()

    print(table.getAttr("x").astype(int))
    print(u.getAttr("x"))
    print(int(model.ObjVal))

    matrix = table.getAttr("x")
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
                if matrix[k, i, j] > 0:
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
except gp.GurobiError as e:
    print('Error code ' + str(e.errno) + ": " + str(e))
