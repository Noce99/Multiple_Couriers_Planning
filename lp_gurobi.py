import numpy as np
import gurobipy as gp
from gurobipy import GRB
import scipy.sparse as sp
import matplotlib.pyplot as plt

n = 47
m = 3

l = [300, 200, 200, ]

s = [12, 8, 16, 5, 12, 5, 13, 20, 13, 18, 7, 6, 9, 9, 4, 25, 5, 17, 3, 16, 25, 21, 14, 19, 14, 6, 16, 9, 20, 13, 10, 16, 19, 22, 14, 10, 11, 15, 13, 15, 8, 22, 24, 3, 25, 19, 21, ]

x = [-30, -31, 52, -13, -67, 49, 5, -65, -4, 23, 25, -43, -77, -21, -52, -41, -92, -65, 19, -41, -38, 24, -43, -35, -55, -49, 57, -23, -57, -39, -17, -12, -47, 16, 1, -26, 4, -51, -23, -71, -8, 12, -19, -12, 30, 12, -38, -10, ]
y = [64, 5, 5, 69, 68, 6, 22, 77, -2, 12, 6, -26, 99, 58, 7, 51, 28, 30, 97, 83, -33, 29, 20, -25, 14, 33, 24, 55, 73, -4, 20, 12, 98, 9, 7, 30, 15, -23, -10, -19, 32, -25, -24, 12, 12, -56, -22, 20, ]

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

