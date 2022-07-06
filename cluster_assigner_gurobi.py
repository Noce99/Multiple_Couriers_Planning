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

#Getting radiant sections division
NUM_OF_SECTIONS = 100 # If cahnged change also the same constant inside "instGen.py"
content = text.split('\n')[:-1]
#print(content)
sections = [content[i][2:-1] for i in range(len(content)) if content[i][0] == '%' and content[i][2] != 'l']
for i in range(len(sections)):
    if sections[i] != '':
        sections[i] = sections[i].split(',')
        for ii in range(len(sections[i])):
            sections[i][ii] = int(sections[i][ii])
    else:
        sections[i] = []
sections_weight = sections.pop()

gp.setParam("PoolSearchMode", 2) # Cerca meglio le soluzioni intermedie
gp.setParam("TimeLimit", 300)# Dopo 5 minuti si ferma e mostra il meglio che ha ottenuto
try:
    model = gp.Model("Cluster_Assigner")
    divisor = model.addMVar(shape=(m), vtype=GRB.INTEGER, name="divisor")
    divisor_expanded = model.addMVar(shape=(m, NUM_OF_SECTIONS), vtype=GRB.INTEGER, name="divisor")
    couriers_assignement = model.addMVar(shape=(m, m), lb=1, ub=m+1, vtype=GRB.INTEGER, name="couriers_assignement")

    for k in range(m-1):
        model.addConstr(divisor[k] <= divisor[k+1])


    for k in range(m):
        for i in range(NUM_OF_SECTIONS):
            model.addConstr(divisor_expanded[k, i] == divisor[k])
    

    for k in range(m):
        model.addConstr(sum(couriers_assignement[k][kk] for kk in range(m)) == 1)

    for k in range(m):
        model.addConstr(sum(sections_weight[i] for i in range(NUM_OF_SECTIONS) if i >= divisor[k] and i <= divisor[k+1]) <= sum(l[kk]*couriers_assignement[k][kk] for kk in range(m)))

    """
    means = model.addMVar(shape=(m), vtype=GRB.INTEGER, name="means")
    for k in range(m):
        model.addConstr(means[k]*sum(table[k, i] for i in range(NUM_OF_SECTIONS)) - sum(table[k, i]*i for i in range(NUM_OF_SECTIONS)) <= 2)

    for k in range(m):
        model.addConstr(sum(table[k, i]*i-means[k] for i in range(NUM_OF_SECTIONS)) <= 25)
        model.addConstr(sum(table[k, i]*i-means[k] for i in range(NUM_OF_SECTIONS)) >= -25)
        pass
    """

    for k in range(m):
        model.addConstr()

    model.setObjective(1, GRB.MINIMIZE)
    # Optimize model
    model.optimize()

    print(table.getAttr("x").astype(int))
    print(int(model.ObjVal))

    div = divisor.getAttr("x")
    cour_ass = couriers_assignement.getAttr("x")

    print("divisor: [", end="")
    for k in range(m):
        print(div[k].getAttr("x"), end=", ")
    print("]")
    print("couriers_assignement: [", end="")
    for k in range(m):
        print(cour_ass[k].getAttr("x"), end=", ")
    print("]")
    """
    colors = [f"C{i}" for i in range(m)]
    for i in range(NUM_OF_SECTIONS):
        for k in range(m):
            if matrix[k, i]:
                for ii in range(len(sections[i])):
                    plt.gca().add_patch(plt.Circle((x[sections[i][ii]],y[sections[i][ii]]), 0.1, color=colors[k]))
                break

    plt.gca().add_patch(plt.Circle((x[len(x)-1], y[len(y)-1]), 0.05, color='r'))
    plt.xlim(min(x)-2,max(x)+2)
    plt.ylim(min(y)-2,max(y)+2)
    plt.show()
    """
except gp.GurobiError as e:
    print('Error code ' + str(e.errno) + ": " + str(e))
quit()
