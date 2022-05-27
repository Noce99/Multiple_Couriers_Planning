import numpy as np
import gurobipy as gp
from gurobipy import GRB
import scipy.sparse as sp
import matplotlib.pyplot as plt

n = 20
m = 2

l = [10, 10, ]

s = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, ]

x = [1, 4, 2, 1, 0, 0, 2, 2, 3, 3, 0, 3, 1, 3, 4, 1, 3, 4, 1, 2, 2, ]
y = [3, 1, 3, 1, 3, 2, 4, 1, 3, 2, 1, 0, 2, 4, 3, 4, 1, 2, 0, 0, 2, ]

N = n + 1

D = np.array([[0 for j in range(N)] for i in range(N)])

for i in range(N):
    for j in range(N):
        D[i, j] = abs(x[i] - x[j]) + abs(y[i] - y[j])

try:
    model = gp.Model("MCP")


    table = model.addMVar(shape=(m, N, N), vtype=GRB.BINARY, name="table")
    u = model.addMVar(shape=(N), lb=0, ub=N+1, vtype=GRB.INTEGER, name="u")
    model.setObjective(sum(D[i, j]*table[k, i, j] for i in range(N) for j in range(N) for k in range(m)), GRB.MINIMIZE)
    
    for i in range(N):
        for k in range(m):
            model.addConstr(table[k,i,i] == 0)
            model.addConstr(sum(table[k,i,j] for j in range(N)) == sum(table[k,j,i] for j in range(N)))
    for j in range(N-1):
        model.addConstr(sum(table[k, i, j] for k in range(m) for i in range(N)) == 1)
    for k in range(m):
        model.addConstr(sum(table[k, N-1, j] for j in range(N-1)) == 1)
        model.addConstr(sum(table[k, j, N-1] for j in range(N-1)) == 1)
        model.addConstr(sum(table[k, i,j]*s[j] for i in range(N) for j in range(N-1)) <= l[k])
    
    for i in range(N-1):
        for j in range(N-1):
            for k in range(m):
                model.addConstr(table[k, i, j]*u[j] >= table[k, i, j]*(u[i]+1))
                pass
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

