import numpy as np
import matplotlib.pyplot as plt
import sys
import time
import subprocess
import tempfile
from itertools import combinations
from z3 import *
import math

semplification = False
if len(sys.argv) < 2:
    quit()
try:
    istanza = int(sys.argv[1])
    if len(sys.argv) > 2:
        semplification = bool(sys.argv[2]) # Vero per qualunque testo
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
content[8] = content[8][1:]
content[9] = content[9][1:]
content[10] = content[10][1:]
content[11] = content[11][1:-2]
content[12] = content[12][1:-2]

if not semplification:
    n = int(content[1])
else:
    n = int(content[7])
m = int(content[0])

l = [int(L) for L in content[2].split(',')]
if not semplification:
    s = [int(L) for L in content[3].split(',')]
    x = [int(L) for L in content[4].split(',')]
    y = [int(L) for L in content[5].split(',')]
    w = [int(L) for L in content[3].split(',')]
else:
    s = [int(L) for L in content[8].split(',')]
    all_s = [int(L) for L in content[3].split(',')]
    all_x = [int(L) for L in content[4].split(',')]
    all_y = [int(L) for L in content[5].split(',')]
    x = [float(L) for L in content[9].split(',')]
    y = [float(L) for L in content[10].split(',')]
    w = [int(L) for L in content[3].split(',')]

reconstructor_x = [L.strip()[1:-1] for L in content[11].split(';')]
reconstructor_y = [L.strip()[1:-1] for L in content[12].split(';')]
for i in range(len(reconstructor_x)):
    try:
        reconstructor_x[i] = [int(L) for L in reconstructor_x[i].split(',')]
        reconstructor_y[i] = [int(L) for L in reconstructor_y[i].split(',')]
    except:
        pass

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

model = SolverFor("AUFLIRA")
#model = Optimize()

obj = Int('obj')

# VARIABLES
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

# Exactly one courier enters and leaves each item
for i in NODES:
    model.add(PbEq([(table[i][j],1) for j in NODES], 1))
    model.add(PbEq([(table[j][i],1) for j in NODES], 1))

# No elements on the diagonal
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
        #model.add(table[i, j]*u[j] >= table[i, j]*(u[i]+1))
        model.add(Implies(table[i][j], order[i] < order[j]))

model.add(obj == Sum([If(table[i][j], 1, 0)*D[i][j] for i in NODES for j in NODES]))
#model.add(Sum([If(table[i][j], 1, 0)*D[i][j] for i in NODES for j in NODES]) <= best_obj)
#model.minimize(obj)

# model.set("sat.pb.solver", "solver")
best_obj = 0
while model.check() == sat:
    local_model = model.model()
    print(f"OBJ: {local_model[obj]}")
    if best_obj == 0:
        best_obj = int(local_model[obj].as_long())-1
    if int(local_model[obj].as_long()) < best_obj:
        best_obj = int(local_model[obj].as_long())-1
    model.add(Or([courier[k][j] != local_model[courier[k][j]] for k in COURIERS for j in ITEMS]))
    model.add(Sum([If(table[i][j], 1, 0)*D[i][j] for i in NODES for j in NODES]) <= best_obj)

print("Completed!")

#print(s.check())
#print(s.model())


for i in range(N):
    for j in range(N):
        if local_model[table[i][j]]:
            print(1, end=" ")
        else:
            print(0, end=" ")
    print("")
print("\n")

couriers_modified = [0 for i in ITEMS]
print("Couriers")
for k in COURIERS:
    for j in ITEMS:
        if local_model[courier[k][j]]:
            print(1, end=" ")
            couriers_modified[j] = k
        else:
            print(0, end=" ")
    print("")
print("\n")
print(f"Couriers modifed: \n{couriers_modified}")

"""
for i in range(N):
    for j in range(N):
        print(D[i, j]*row[0][i][j], end=" ")
    print("")
"""

"""
print(distancestring)
distanzacalcolatapy = 0
for k in range(m):
    for i in range(N):
        for j in range(N):
            distanzacalcolatapy += D[i, j]*table[k][i][j]
"""

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
"""
for k in range(m):
    x1s.clear()
    y1s.clear()
    x2s.clear()
    y2s.clear()
"""
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
plt.show()

if semplification:
    post_optimization = 0
    print("INIZIO OTIMMIZAZIONE FINALE")
    who_have_what = [[n] for k in range(m)]
    """
    for k in range(m):
        for i in range(N):
            for j in range(N):
                if solver.Value(table[k][i][j]) == 1 and i != j:
                    who_have_what[k].append(i)
    """
    for i in ITEMS:
        who_have_what[couriers_modified[i]].append(i)

    #print("Who have_what: \n", who_have_what, "---------------")
    x_for_each = [[] for k in range(m)]
    y_for_each = [[] for k in range(m)]
    for k in range(m):
        for i in range(len(who_have_what[k])):
            for ii in range(len(reconstructor_x[who_have_what[k][i]])):
                x_for_each[k].append(reconstructor_x[who_have_what[k][i]][ii])
                y_for_each[k].append(reconstructor_y[who_have_what[k][i]][ii])
    #print(x_for_each)
    color_i = 1
    color = 'C1'
    for k in range(m):
        N_opt = len(x_for_each[k])
        D = [[0 for j in range(N_opt)] for i in range(N_opt)]
        for i in range(N_opt):
            for j in range(N_opt):
                D[i][j] = int(abs(x_for_each[k][i] - x_for_each[k][j]) + abs(y_for_each[k][i] - y_for_each[k][j]))

        #------------------------------------------------------------------------
        ITEMS = list(range(N_opt-1))
        NODES = list(range(N_opt))

        model = SolverFor("AUFLIRA")
        #model = Optimize()

        obj = Int('obj')

        # VARIABLES
        table = []
        for i in NODES:
            rows = []
            for j in NODES:
                rows.append(Bool(f't[{i},{j}]'))
            table.append(rows)

        order = IntVector('order', N_opt-1)
        obj = Int('obj')

        # Exactly one courier enters and leaves each item
        for i in NODES:
            model.add(PbEq([(table[i][j],1) for j in NODES], 1))
            model.add(PbEq([(table[j][i],1) for j in NODES], 1))

        # No elements on the diagonal
        for i in ITEMS:
            model.add(table[i][i] == False)

        for i in NODES:
            for j in NODES:
                if i != j:
                    model.add(Implies(table[j][i], table[i][j] == False))

        model.add(order[0] == 1)
        for i in ITEMS:
            for j in ITEMS:
                #model.add(table[i, j]*u[j] >= table[i, j]*(u[i]+1))
                model.add(Implies(table[i][j], order[i] < order[j]))

        model.add(obj == Sum([If(table[i][j], 1, 0)*D[i][j] for i in NODES for j in NODES]))
        #model.add(Sum([If(table[i][j], 1, 0)*D[i][j] for i in NODES for j in NODES]) <= best_obj)
        #model.minimize(obj)

        # model.set("sat.pb.solver", "solver")
        best_obj = 0
        while model.check() == sat:
            local_model = model.model()
            print(f"Optimization-OBJ: {local_model[obj]}")
            if best_obj == 0:
                best_obj = int(local_model[obj].as_long())-1
            if int(local_model[obj].as_long()) < best_obj:
                best_obj = int(local_model[obj].as_long())-1
            model.add(Or([table[i][j] != local_model[table[i][j]] for i in NODES for j in NODES]))
            model.add(Sum([If(table[i][j], 1, 0)*D[i][j] for i in NODES for j in NODES]) <= best_obj)

        print("Completed!")

        #--------------------------------------------------------------------

        print(f"Done optimization for {k}-courier")
        print(f"N_opt {N_opt}")
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
        print("----------------------------------")
    print(f"{file}-SMT Post optimization: {post_optimization}")
    plt.xlim(min(all_x)-2,max(all_x)+2)
    plt.ylim(min(all_y)-2,max(all_y)+2)
    plt.show()
    #plt.savefig(f'Results/Or_Tools/Or_tools_{file}.png')
    plt.clf()
