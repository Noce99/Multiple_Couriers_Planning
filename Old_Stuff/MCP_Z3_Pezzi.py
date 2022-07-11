import numpy as np
import matplotlib.pyplot as plt
import sys
import time
import subprocess
import tempfile
from itertools import combinations
from z3 import *
import math
import gurobipy as gp
from gurobipy import GRB
import scipy.sparse as sp

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

gp.setParam("PoolSearchMode", 2) # Cerca meglio le soluzioni intermedie
gp.setParam("TimeLimit", 300)# Dopo 5 minuti si ferma e mostra il meglio che ha ottenuto
try:
    model = gp.Model("MCP_Select_Items")
    model.params.NonConvex = 2

    table = model.addMVar(shape=(m, N), vtype=GRB.BINARY, name="table")

    for i in range(n):
        model.addConstr(sum(table[k, i] for k in range(m)) == 1)

    for k in range(m):
        model.addConstr(table[k, N-1] == 1)

    means_positions_x = model.addMVar(shape=(m), lb=-500, ub=500, vtype=GRB.CONTINUOUS, name="means_positions_x")
    means_positions_y = model.addMVar(shape=(m), lb=-500, ub=500, vtype=GRB.CONTINUOUS, name="means_positions_y")
    num = model.addMVar(shape=(m), lb=1, ub=1000, vtype=GRB.INTEGER, name="num")
    for k in range(m):
        model.addConstr(num[k] == sum(table[k, i] for i in range(N)))
        model.addConstr(means_positions_x[k]*num[k] - sum(table[k, i]*x[i] for i in range(N)) <= 0.01)
        model.addConstr(means_positions_x[k]*num[k] - sum(table[k, i]*x[i] for i in range(N)) >= -0.01)
        model.addConstr(means_positions_y[k]*num[k] - sum(table[k, i]*y[i] for i in range(N)) <= 0.01)
        model.addConstr(means_positions_y[k]*num[k] - sum(table[k, i]*y[i] for i in range(N)) >= -0.01)

    partial_dispersion = model.addMVar(shape=(m, N), vtype=GRB.CONTINUOUS, name="partial_dispersion")
    for k in range(m):
        for i in range(N):
            model.addConstr(partial_dispersion[k, i] - (means_positions_x[k]-x[i])**2 -
            (means_positions_y[k]-y[i])**2 <= 0.01)
            model.addConstr(partial_dispersion[k, i] - (means_positions_x[k]-x[i])**2 -
            (means_positions_y[k]-y[i])**2 >= -0.01)

    total_dispersion = sum(partial_dispersion[k, i]*table[k, i] for k in range(m) for i in range(N))

    model.setObjective(total_dispersion, GRB.MINIMIZE)
    # Optimize model
    model.optimize()

    print(table.getAttr("x").astype(int))
    print(int(model.ObjVal))

    matrix = table.getAttr("x")



    print("Num: [", end="")
    for k in range(m):
        print(num[k].getAttr("x"), end=", ")
    print("]")
    print("Means_x: [", end="")
    for k in range(m):
        print(means_positions_x[k].getAttr("x"), end=", ")
    print("]")
    print("Means_y: [", end="")
    for k in range(m):
        print(means_positions_y[k].getAttr("x"), end=", ")
    print("]")

    print("partial_dispersion: [", end="")
    for k in range(m):
        for i in range(n):
            print(partial_dispersion[k, i].getAttr("x")*matrix[k, i], end=", ")
        print("")
    print("]")

    print(f"total_dispersion: {int(model.ObjVal)}")


    colors = [f"C{i}" for i in range(m)]
    for i in range(n):
        for k in range(m):
            if matrix[k, i]:
                plt.gca().add_patch(plt.Circle((x[i],y[i]), 0.1, color=colors[k]))
                break
    for k in range(m):
        # print(float(model[means_positions_x[k]].as_decimal(3)))
        # print(type(float(model[means_positions_x[k]].as_decimal(3))))
        plt.gca().add_patch(plt.Circle((means_positions_x[k].getAttr("x"),
         means_positions_y[k].getAttr("x")), 0.01, color=colors[k]))

    plt.gca().add_patch(plt.Circle((x[len(x)-1], y[len(y)-1]), 0.05, color='r'))
    plt.xlim(min(x)-2,max(x)+2)
    plt.ylim(min(y)-2,max(y)+2)
    plt.show()
except gp.GurobiError as e:
    print('Error code ' + str(e.errno) + ": " + str(e))

quit()



















o = Optimize()

# Creo un vettore "colonna" per item (numero di elemeti pari al numero di
# couriers) in cui la riga i-esima rappresenta l'i-esimo courier,
# se è uguale a 1 allora quel courier passa a prendere quel pacco.

COURIERS = []
for i in range(n):
    COURIERS.append(BoolVector(f'item{i}', m))

for i in range(n):
    o.add(PbEq([(x,1) for x in COURIERS[i]], 1))

# Calcolo la distanza dalla posizione media degli items tra i courier e provo
# a massimizarla


# Dentro "means_positions_x[k]" ho la media delle x degli elementi trasportati
# dal courier k (uguale per "means_positions_y[k]")
means_positions_x = [Int(f'means_x_{k}') for k in range(m)]
for k in range(m):
    o.add(means_positions_x[k] == Sum([COURIERS[i][k]*x[i] for i in range(n)])/
    Sum([COURIERS[i][k] for i in range(n)]))
means_positions_y = [Int(f'means_y_{k}') for k in range(m)]
for k in range(m):
    o.add(means_positions_y[k] == Sum([COURIERS[i][k]*y[i] for i in range(n)])/
    Sum([COURIERS[i][k] for i in range(n)]))

dispersion = [Int(f'dispersion_{k}') for k in range(m)]
for k in range(m):
    o.add(dispersion[k] == Sum([COURIERS[i][k]*((float(x[i])-means_positions_x[k])*(float(x[i])-means_positions_x[k])
    + (float(y[i])-means_positions_y[k])*(float(y[i])-means_positions_y[k])) for i in range(n)]))

total_dispersion = Int(f'total_dispersion')
o.add(total_dispersion == Sum(dispersion))

"""
# Dentro "all_means_x" calcolo la media delle posizioni medie di tutti i
# couriers. (uguale per "all_means_y")
all_means_x = Real('all_means_x')
all_means_y = Real('all_means_y')
o.add(all_means_x == Sum([means_positions_x[k] for k in range(m)])/m)
o.add(all_means_y == Sum([means_positions_y[k] for k in range(m)])/m)

# Dentro a "distance_from_all_means" calcola la somma delle distanze tra la
# "all_means" e la media della posizione degli item di ciascun courier
distance_from_all_means = Real('distance_from_all_means')
o.add(distance_from_all_means == Sum([
(means_positions_x[k]-all_means_x)*(means_positions_x[k]-all_means_x) +
(means_positions_y[k]-all_means_y)*(means_positions_y[k]-all_means_y)
 for k in range(m)]))
"""
"""
obj = Int('obj')

row = []
for k in range(m):
    x = []
    for i in range(N):
        x.append(BoolVector(f'row{k}__{i}', N))
    row.append(x)

col = []
for k in range(m):
    y = []
    for i in range(N):
        y.append(BoolVector(f'col{k}__{i}', N))
    col.append(y)

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
"""
o.minimize(total_dispersion)

# o.set("sat.pb.solver", "solver")

if o.check() == sat:
    model = o.model()
    #print(m)
else:
    print("unsat")
    quit()

#print(o.check())
#print(o.model())

for k in range(m):
    print(f"Courier {k}:", end ="\t")
    for i in range(n):
        if model[COURIERS[i][k]]:
            print(1, end=" ")
        else:
            print(0, end=" ")
    print("")

print("Means_x: [", end="")
for k in range(m):
    print(model[means_positions_x[k]], end=", ")
print("]")
print("Means_y: [", end="")
for k in range(m):
    print(model[means_positions_y[k]], end=", ")
print("]")
print("Dispersions: [", end="")
for k in range(m):
    print(model[dispersion[k]], end=", ")
print("]")
print(f"total_dispersion: {model[total_dispersion]}")

"""
print(f"all_means_x: {model[all_means_x]}")
print(f"all_means_y: {model[all_means_y]}")
print(f"distance_from_all_means: {model[distance_from_all_means]}")
"""

colors = [f"C{i}" for i in range(m)]
for i in range(n):
    for k in range(m):
        if model[COURIERS[i][k]]:
            plt.gca().add_patch(plt.Circle((x[i],y[i]), 0.1, color=colors[k]))
            break
for k in range(m):
    # print(float(model[means_positions_x[k]].as_decimal(3)))
    # print(type(float(model[means_positions_x[k]].as_decimal(3))))
    plt.gca().add_patch(plt.Circle((int(model[means_positions_x[k]].as_long()),
     int(model[means_positions_y[k]].as_long())), 0.01, color=colors[k]))

plt.gca().add_patch(plt.Circle((x[len(x)-1], y[len(y)-1]), 0.05, color='r'))
plt.xlim(min(x)-2,max(x)+2)
plt.ylim(min(y)-2,max(y)+2)
plt.show()

quit()

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
"""
