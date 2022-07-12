import numpy as np
import matplotlib.pyplot as plt
from ortools.sat.python import cp_model
import sys
import time
# ------------------------------------------------------------------------------
# This is our CP model and we have used the ortools lib to build it
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

N = n + 1

ITEMS = list(range(n))
NODES = list(range(N))
COURIERS = list(range(m))

D = np.array([[0 for j in range(N)] for i in range(N)])
for i in range(N):
    for j in range(N):
        D[i, j] = abs(x[i] - x[j]) + abs(y[i] - y[j])
# --------------------3--------------------
# --------------------4--------------------
# ------------------MODEL------------------
# There we have the first model that run on aggregated items
model = cp_model.CpModel()

# VARIABLES
# We simply have a 3D Matrix [k*N*N]
table = []
for k in COURIERS:
    rows = []
    for i in NODES:
        cols = []
        for j in NODES:
            cols.append(model.NewBoolVar(name=f't[{k},{i},{j}]'))
        rows.append(cols)
    table.append(rows)

# CONSTRAINTS
# Exactly One - all items are delivered
for i in ITEMS:
    model.AddExactlyOne([table[k][i][j] for k in COURIERS for j in NODES if j != i])
    model.AddExactlyOne([table[k][j][i] for k in COURIERS for j in NODES if j != i])

# All the couriers leave the depot
for k in COURIERS:
    model.Add(table[k][N-1][N-1] == 0)

# Weights - do not overcome the capacity limit
for k in COURIERS:
    model.Add(sum([table[k][i][j]*s[j] for i in NODES for j in range(N-1) if i != j]) <= l[k])

# Circuit - Hamiltonian path
for k in COURIERS:
    arcs = []
    for i in NODES:
        for j in NODES:
            arcs.append((i, j, table[k][i][j]))
    model.AddCircuit(arcs)

# OBJECTIVE FUNCTION - minimize the distance
obj = cp_model.LinearExpr.Sum([table[k][i][j]*D[i, j] for k in COURIERS for i in NODES for j in NODES])

model.Add(obj >= lower_boud)

# MINIMIZATION OF THE OBJ FUNCTION
model.Minimize(obj)
solver = cp_model.CpSolver()
solver.parameters.max_time_in_seconds = 300.0 # Time Limit of 5 minutes
status = solver.Solve(model)
# --------------------4--------------------
if status == cp_model.OPTIMAL or status == cp_model.FEASIBLE:
    # --------------------5--------------------
    # If the model is FEASIBLE we print it
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
    for k in range(m):
        x1s.clear()
        y1s.clear()
        x2s.clear()
        y2s.clear()
        for i in range(N):
            for j in range(N):
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
    plt.savefig(f'Results/Or_Tools/Or_tools_{file}_Pre_Optimization.png')
    plt.clf()
    # --------------------5--------------------
    # --------------------6--------------------
    # There we star the last optimization phase calculating for the original
    # objects the couriers at witch they belong
    post_optimization = 0
    who_have_what = [[] for k in range(m)]
    for k in range(m):
        for i in range(N):
            for j in range(N):
                if solver.Value(table[k][i][j]) == 1 and i != j:
                    who_have_what[k].append(i)
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
        # ------------------MODEL------------------
        # There we create a LP model for each courier that minimize the distance it travels.
        # We only modify the order at witch items are collected and do not
        # change at which courier each item belongs.
        N_opt = len(x_for_each[k])

        D = np.array([[0 for j in range(N_opt)] for i in range(N_opt)])
        for i in range(N_opt):
            for j in range(N_opt):
                D[i, j] = abs(x_for_each[k][i] - x_for_each[k][j]) + abs(y_for_each[k][i] - y_for_each[k][j])

        ITEMS = list(range(N_opt-1))
        NODES = list(range(N_opt))
        model = cp_model.CpModel()

        # We create our 3D Matrix
        table = []
        table.clear()
        for i in NODES:
            cols = []
            for j in NODES:
                cols.append(model.NewBoolVar(name=f't[{i},{j}]'))
            table.append(cols)

        # CONSTRAINTS - same of the ones above (excluding weights)
        for i in ITEMS:
            model.AddExactlyOne([table[i][j] for j in NODES if j != i])
            model.AddExactlyOne([table[j][i] for j in NODES if j != i])

        model.Add(table[N_opt-1][N_opt-1] == 0)

        arcs = []
        for i in NODES:
            for j in NODES:
                arcs.append((i, j, table[i][j]))
        model.AddCircuit(arcs)

        # OBJECTIVE FUNCTION
        obj = cp_model.LinearExpr.Sum([table[i][j]*D[i, j] for i in NODES for j in NODES])

        # MINIMIZATION OF THE OBJ FUNCTION
        model.Minimize(obj)
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = 20.0 # 20 Second of Time Limit
        status = solver.Solve(model)
        print(f"Done optimization for {k}-courier")
        # --------------------7--------------------
        # --------------------8--------------------
        # There we print out final result after the second optimization
        post_optimization += int(solver.ObjectiveValue())
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
                if solver.Value(table[i][j]) == 1:
                    x1s.append(x_for_each[k][i])
                    y1s.append(y_for_each[k][i])
                    x2s.append(x_for_each[k][j]-x_for_each[k][i])
                    y2s.append(y_for_each[k][j]-y_for_each[k][i])
        plt.quiver(x1s, y1s, x2s, y2s, angles='xy', scale_units='xy', color=[color], scale=1, width=0.003)
        color_i += 1
        color = 'C'+str(color_i)
        # --------------------8--------------------
        # --------------------9--------------------
        # There we print solution in the desired format:
        for j in range(N_opt):
            if solver.Value(table[N_opt-1][j]) == 1:
                next_one = j
                final_i_for_each[k].append(who_have_what_after_clustering[k][next_one])
                break
        while next_one != N_opt-1:
            for j in range(N_opt):
                if solver.Value(table[next_one][j]) == 1:
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
    print(f"{file}-OR-TOOLS OBJ Post optimization: {post_optimization}")
    plt.xlim(min(all_x)-2,max(all_x)+2)
    plt.ylim(min(all_y)-2,max(all_y)+2)
    plt.savefig(f'Results/Or_Tools/Or_tools_{file}.png')
    plt.clf()
else:
    print('No solution found.')
