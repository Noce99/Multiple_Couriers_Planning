import numpy as np
import gurobipy as gp
from gurobipy import GRB
import scipy.sparse as sp
import matplotlib.pyplot as plt
import sys
import time
# ------------------------------------------------------------------------------
# This is our LP model and we have used the gurobipy lib to build it
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

D = np.array([[0 for j in range(N)] for i in range(N)])
for i in range(N):
    for j in range(N):
        D[i, j] = abs(x[i] - x[j]) + abs(y[i] - y[j])

# --------------------3--------------------
# --------------------4--------------------
# ------------------MODEL------------------
# There we have the first model that run on aggregated items
gp.setParam("OutputFlag", 0) # Suppres Output
gp.setParam("PoolSearchMode", 2) # To find better intermediary solution
gp.setParam("TimeLimit", 300) # Time Limit of 5 minutes

try:
    # Model Initialization
    model = gp.Model("LP_Model")

    # We have 2 variables, a 3D matrix as in CP and a 'u' Vector to remove loops
    table = model.addMVar(shape=(m, N, N), vtype=GRB.BINARY, name="table")
    u = model.addMVar(shape=(N), lb=1, ub=N, vtype=GRB.INTEGER, name="u")

    # Obj definition
    obj = sum(D[i, j]*table[k, i, j] for i in range(N) for j in range(N) for k in range(m))

    model.addConstr(obj >= lower_boud)
    model.setObjective(obj, GRB.MINIMIZE)

    # Constraints
    for i in range(N):
        for k in range(m):
            # Each courier leaves the depot
            model.addConstr(table[k,i,i] == 0)
            # If an item is reached, it is also leaved by the same courier
            model.addConstr(sum(table[k,i,j] for j in range(N)) == sum(table[k,j,i] for j in range(N)))

    # Every item is delivered
    for j in range(N-1):
        model.addConstr(sum(table[k, i, j] for k in range(m) for i in range(N)) == 1)


    for k in range(m):
        # Start from the depot and come back to it at the end
        model.addConstr(sum(table[k, N-1, j] for j in range(N-1)) == 1)
        model.addConstr(sum(table[k, j, N-1] for j in range(N-1)) == 1)
        # Weights constraint
        model.addConstr(sum(table[k, i, j]*s[j] for i in range(N) for j in range(N-1)) <= l[k])

    # Sub-tours (Loops) elimination
    for i in range(N):
        for j in range(N-1):
            for k in range(m):
                model.addConstr(u[N-1] == 1)
                model.addConstr(table[k, i, j]*u[j] >= table[k, i, j]*(u[i]+1))

    # Model Optimization
    model.optimize()

    # There we check if we have gotten a solution and if yes we put results
    # inside the matrix variable
    try:
        matrix = table.getAttr("x")
        pre_optimization = int(model.ObjVal)
    except:
        quit()
    # --------------------4--------------------
    # --------------------5--------------------
    # There we print the obtained result
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
    plt.savefig(f'Results/Gurobi/Gurobi_{file}_Pre_Optimization.png')
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
                if matrix[k, i, j] > 0:
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
        # We only modify the order at witch items are collected and don't
        # changing at witch courier each item belong.

        N_opt = len(x_for_each[k])

        D = np.array([[0 for j in range(N_opt)] for i in range(N_opt)])
        for i in range(N_opt):
            for j in range(N_opt):
                D[i, j] = abs(x_for_each[k][i] - x_for_each[k][j]) + abs(y_for_each[k][i] - y_for_each[k][j])

        gp.setParam("OutputFlag", 0) # Suppres Output
        gp.setParam("PoolSearchMode", 2)
        gp.setParam("TimeLimit", 20) # 20 Second of Time Limit

        # Model Initialization
        model = gp.Model(f"ottimizzazione_{k}")

        # We have 2 variables, a 3D matrix as in CP and a u Vector to remove loops
        table = model.addMVar(shape=(N_opt, N_opt), vtype=GRB.BINARY, name="table")
        u = model.addMVar(shape=(N_opt), lb=1, ub=N_opt, vtype=GRB.INTEGER, name="u")

        # Obj definition
        obj = sum(D[i, j]*table[i, j] for i in range(N_opt) for j in range(N_opt))
        model.setObjective(obj, GRB.MINIMIZE)

        # Constraints - same of the ones above (excluding weights)
        for i in range(N_opt):
                model.addConstr(table[i,i] == 0)
                model.addConstr(sum(table[i,j] for j in range(N_opt)) == sum(table[j,i] for j in range(N_opt)))

        for j in range(N_opt):
            model.addConstr(sum(table[i, j] for i in range(N_opt)) == 1)
            model.addConstr(sum(table[j, i] for i in range(N_opt)) == 1)

        for i in range(N_opt):
            for j in range(N_opt-1):
                model.addConstr(u[N_opt-1] == 1)
                model.addConstr(table[i, j]*u[j] >= table[i, j]*(u[i]+1))

        # Model Optimization
        model.optimize()
        print(f"Done optimization for {k}-courier.")
        # --------------------7--------------------
        # --------------------8--------------------
        # There we print out final result after the second optimization
        post_optimization += int(model.ObjVal)
        matrix = table.getAttr("x")
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
                if matrix[i, j] > 0.5:
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
            if matrix[N_opt-1, j] > 0.5:
                next_one = j
                final_i_for_each[k].append(who_have_what_after_clustering[k][next_one])
                break
        while next_one != N_opt-1:
            for j in range(N_opt):
                if matrix[next_one, j] > 0.5:
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
    print(f"{file}-GUROBI Post optimization: {post_optimization}")
    plt.xlim(min(all_x)-2,max(all_x)+2)
    plt.ylim(min(all_y)-2,max(all_y)+2)
    plt.savefig(f'Results/Gurobi/Gurobi_{file}.png')
    plt.clf()
except gp.GurobiError as e:
    print('Error code ' + str(e.errno) + ": " + str(e))
