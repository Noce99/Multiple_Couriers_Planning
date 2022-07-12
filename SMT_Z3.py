import numpy as np
import matplotlib.pyplot as plt
import sys
import time
import subprocess
import tempfile
from itertools import combinations
from z3 import *
import math
# ------------------------------------------------------------------------------
# This is our SMT model and we have used the z3 lib to build it
# Author: Enrico Mannocci enrico.mannocci@studio.unibo.it),
# Riccardo Paolini (riccardo.paolini5@studio.unibo.it) &
# Matteo Periani (matteo.periani2@studio.unibo.it)
# ------------------------------------------------------------------------------
# --------------------1--------------------
# There we get the argument that specifie the istance we want to solve
if len(sys.argv) < 2:
    print("You need at least a parameter to detect the instance.")
    quit()
try:
    istanza = int(sys.argv[1])
except:
    print("Put a number between 1 and 11 to run an istance.")
    quit()
# --------------------1--------------------
# --------------------2--------------------
# There we get the preprocessed data about the selected instance
# In the end we have:
# n                 ->  [int]                   Number of Nodes (after aggregation)
# m                 ->  [int]                   Number of couriers
# l                 ->  [list of int]           Max load for each courier
# s                 ->  [list of int]           Weight of each Item (after aggregation)
# x                 ->  [list of float]         X coordinates for each Item (after aggregation)
# y                 ->  [list of float]         Y coordinates for each Item (after aggregation)
# all_s             ->  [list of int]           Weight of each Item (Before aggregation)
# all_x             ->  [list of float]         X coordinates for each Item (Before aggregation)
# all_y             ->  [list of float]         Y coordinates for each Item (Before aggregation)
# reconstructor_x   ->  [list of list of int]   X coordinates for each item (Before aggregation) aggregated in clusters (list)
# reconstructor_y   ->  [list of list of int]   Y coordinates for each item (Before aggregation) aggregated in clusters (list)
# lower_boud        ->  [int]                   Lowe Bound Calculated with some constraint relaxation for our OBJ Function
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
content[13] = content[13][1:-2]
n = int(content[7])
m = int(content[0])
l = [int(L) for L in content[2].split(',')]
all_s = [int(L) for L in content[3].split(',')]
all_x = [int(L) for L in content[4].split(',')]
all_y = [int(L) for L in content[5].split(',')]
s = [int(L) for L in content[8].split(',')]
x = [float(L) for L in content[9].split(',')]
y = [float(L) for L in content[10].split(',')]
reconstructor_x = [L.strip()[1:-1] for L in content[11].split(';')]
reconstructor_y = [L.strip()[1:-1] for L in content[12].split(';')]
reconstructor = [L.strip()[1:-1] for L in content[13].split(';')]
for i in range(len(reconstructor_x)):
    try:
        reconstructor_x[i] = [int(L) for L in reconstructor_x[i].split(',')]
        reconstructor_y[i] = [int(L) for L in reconstructor_y[i].split(',')]
        reconstructor[i] = [int(L) for L in reconstructor[i].split(',')]
    except:
        pass
# --------------------2--------------------
# --------------------3--------------------
# There we create some important constants from the data we have got in the
# prevous section.
# D[i, j]   ->  Is the Manatthan distaces between item i and item j
x = x + [x[-1]]*(m-1)
y = y + [y[-1]]*(m-1)
N = n + m
ITEMS = list(range(n))
NODES = list(range(N))
COURIERS = list(range(m))
D = [[0 for j in range(N)] for i in range(N)]
for i in range(N):
    for j in range(N):
        if i > n and j > n:
            D[i][j] = int(0)
        elif i > n:
            D[i][j] = int(abs(x[n] - x[j]) + abs(y[n] - y[j]))
        elif j > n:
            D[i][j] = int(abs(x[i] - x[n]) + abs(y[i] - y[n]))
        else:
            D[i][j] = int(abs(x[i] - x[j]) + abs(y[i] - y[j]))
# --------------------3--------------------
# --------------------4--------------------
# There we have the first model that run on aggregated items
# Model Initialization
model = Solver()
# We have three variables: a 2D matrix [n+m * n+m] (table),
# a 2D matrix [m * n] (courier) and a vector for avoiding loops (order)
table = []
for i in NODES:
    rows = []
    for j in NODES:
        rows.append(Bool(f't[{i},{j}]'))
    table.append(rows)
courier = []
for k in COURIERS:
    rows = []
    for i in ITEMS:
        rows.append(Bool(f'courier[{k},{i}]'))
    courier.append(rows)
order = IntVector('order', n)
obj = Int('obj')
# Constaints
for i in NODES:
    model.add(PbEq([(table[i][j],1) for j in NODES], 1))
    model.add(PbEq([(table[j][i],1) for j in NODES], 1))
for i in ITEMS:
    model.add(table[i][i] == False)
for i in NODES:
    for j in NODES:
        if i != j:
            model.add(Implies(table[j][i], table[i][j] == False))
for i in range(n, N):
    for j in range(n, N):
        if i != j:
            model.add(table[i][j] == False)
for i in ITEMS:
    model.add(PbEq([(courier[k][i],1) for k in COURIERS], 1))
for i in range(n, N):
    for j in ITEMS:
        model.add(Implies(table[i][j], courier[i-n][j] == True))
for k in COURIERS:
    for i in ITEMS:
        for j in ITEMS:
            model.add(Implies(table[i][j], courier[k][i] == courier[k][j]))
for k in COURIERS:
    model.add(Sum([If(courier[k][j], 1, 0)*s[j] for j in ITEMS]) <= l[k])
model.add(order[0] == 1)
for i in ITEMS:
    for j in ITEMS:
        model.add(Implies(table[i][j], order[i] < order[j]))
# Obj definition
model.add(obj == Sum([If(table[i][j], 1, 0)*D[i][j] for i in NODES for j in NODES]))
# Model Optimization
best_obj = 0
print("OBJ: ")
model.set("timeout", 600*200)
while model.check() == sat:
    local_model = model.model()
    print(f"{local_model[obj]}")
    if best_obj == 0:
        best_obj = int(local_model[obj].as_long())-1
    if int(local_model[obj].as_long()) < best_obj:
        best_obj = int(local_model[obj].as_long())-1
    model.add(Or([courier[k][j] != local_model[courier[k][j]] for k in COURIERS for j in ITEMS]))
    model.add(Sum([If(table[i][j], 1, 0)*D[i][j] for i in NODES for j in NODES]) <= best_obj)
if best_obj == 0:
    quit()
print("Optimized the first Model!")
# --------------------4--------------------
# --------------------5--------------------
# There we print the obtained result, we need to create "couriers_modified" for
# coloring reason
couriers_modified = [0 for i in ITEMS]
for k in COURIERS:
    for j in ITEMS:
        if local_model[courier[k][j]]:
            couriers_modified[j] = k
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
for i in range(N):
    for j in range(N):
        if local_model[table[i][j]]:
            if i<max(ITEMS):
                plt.quiver([x[i]], [y[i]], [x[j]-x[i]], [y[j]-y[i]], angles='xy', scale_units='xy', color=['C'+str(couriers_modified[i])], scale=1, width=0.003)
            else:
                if j<max(ITEMS):
                    plt.quiver([x[i]], [y[i]], [x[j]-x[i]], [y[j]-y[i]], angles='xy', scale_units='xy', color=['C'+str(couriers_modified[j])], scale=1, width=0.003)
color_i += 1
color = 'C'+str(color_i)
plt.xlim(min(x)-2,max(x)+2)
plt.ylim(min(y)-2,max(y)+2)
plt.savefig(f'Results/SMT/SMT_{file}_Pre_Optimization.png')
plt.clf()
# --------------------5--------------------
# --------------------6--------------------
# There we star the last optimization phase calculating for the original
# objects the couriers at witch they belong
post_optimization = 0
who_have_what = [[n] for k in range(m)]
for i in ITEMS:
    who_have_what[couriers_modified[i]].append(i)
x_for_each = [[] for k in range(m)]
y_for_each = [[] for k in range(m)]
who_have_what_after_clustering = [[] for k in range(m)]
for k in range(m):
    for i in range(len(who_have_what[k])):
        for ii in range(len(reconstructor_x[who_have_what[k][i]])):
            x_for_each[k].append(reconstructor_x[who_have_what[k][i]][ii])
            y_for_each[k].append(reconstructor_y[who_have_what[k][i]][ii])
            who_have_what_after_clustering[k].append(reconstructor[who_have_what[k][i]][ii])
# --------------------6--------------------
color_i = 1
color = 'C1'
final_i_for_each = [[] for k in range(m)]
for k in range(m):
    # --------------------7--------------------
    # There we create a SMT model for each couriers minimizing the distance.
    # We only modify the order at witch items are collected and don't
    # changing at witch courier each item belong.
    N_opt = len(x_for_each[k])
    D = [[0 for j in range(N_opt)] for i in range(N_opt)]
    for i in range(N_opt):
        for j in range(N_opt):
            D[i][j] = int(abs(x_for_each[k][i] - x_for_each[k][j]) + abs(y_for_each[k][i] - y_for_each[k][j]))
    ITEMS = list(range(N_opt-1))
    NODES = list(range(N_opt))
    # Model Initialization
    model = Solver()
    # We have two variables: a 2D matrix [N_opt * N_opt] (table) and
    # a vector for avoiding loops (order)
    table = []
    for i in NODES:
        rows = []
        for j in NODES:
            rows.append(Bool(f't[{i},{j}]'))
        table.append(rows)
    order = IntVector('order', N_opt-1)
    obj = Int('obj')
    # Constraints
    for i in NODES:
        model.add(PbEq([(table[i][j],1) for j in NODES], 1))
        model.add(PbEq([(table[j][i],1) for j in NODES], 1))
    for i in ITEMS:
        model.add(table[i][i] == False)
    for i in NODES:
        for j in NODES:
            if i != j:
                model.add(Implies(table[j][i], table[i][j] == False))
    model.add(order[0] == 1)
    for i in ITEMS:
        for j in ITEMS:
            model.add(Implies(table[i][j], order[i] < order[j]))
    # Obj definition
    model.add(obj == Sum([If(table[i][j], 1, 0)*D[i][j] for i in NODES for j in NODES]))
    # Model Optimization
    best_obj = 0
    print(f"Optimization-{k}-OBJ:")
    model.set("timeout", 150*200)
    while model.check() == sat:
        local_model = model.model()
        print(f"{local_model[obj]}")
        if best_obj == 0:
            best_obj = int(local_model[obj].as_long())-1
        if int(local_model[obj].as_long()) < best_obj:
            best_obj = int(local_model[obj].as_long())-1
        model.add(Or([table[i][j] != local_model[table[i][j]] for i in NODES for j in NODES]))
        model.add(Sum([If(table[i][j], 1, 0)*D[i][j] for i in NODES for j in NODES]) <= best_obj)
    if best_obj == 0:
        quit()
    print(f"Done optimization for {k}-courier")
    # --------------------8--------------------
    # There we print out final result after the second optimization
    post_optimization += int(local_model[obj].as_long())
    for i in range(N_opt):
        plt.gca().add_patch(plt.Circle((x_for_each[k][i],y_for_each[k][i]), 0.2, color='b'))
    x1s = []
    y1s = []
    x2s = []
    y2s = []
    x1s.clear()
    y1s.clear()
    x2s.clear()
    y2s.clear()
    for i in range(N_opt):
        for j in range(N_opt):
            if local_model[table[i][j]]:
                x1s.append(x_for_each[k][i])
                y1s.append(y_for_each[k][i])
                x2s.append(x_for_each[k][j]-x_for_each[k][i])
                y2s.append(y_for_each[k][j]-y_for_each[k][i])
    plt.quiver(x1s, y1s, x2s, y2s, angles='xy', scale_units='xy', color=[color], scale=1, width=0.003)
    color_i += 1
    color = 'C'+str(color_i)
    # --------------------8--------------------
    # --------------------9--------------------
    # There we print solution in the desired format
    for j in range(N_opt):
        if local_model[table[N_opt-1][j]]:
            next_one = j
            final_i_for_each[k].append(who_have_what_after_clustering[k][next_one])
            break
    while next_one != N_opt-1:
        for j in range(N_opt):
            if local_model[table[next_one][j]]:
                next_one = j
                if next_one != N_opt-1:
                    final_i_for_each[k].append(who_have_what_after_clustering[k][next_one])
                break
for k in range(m):
    print(f"Courier {k+1}: o -> ", end="")
    for i in range(len(final_i_for_each[k])):
        print(f"d{final_i_for_each[k][i]} -> ", end="")
    print("o")
# --------------------9--------------------
print(f"{file}-SMT Post optimization: {post_optimization}")
plt.xlim(min(all_x)-2,max(all_x)+2)
plt.ylim(min(all_y)-2,max(all_y)+2)
plt.savefig(f'Results/SMT/SMT_{file}.png')
plt.clf()
