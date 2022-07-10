import numpy as np
import matplotlib.pyplot as plt
from ortools.sat.python import cp_model
import sys
import time

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
else:
    s = [int(L) for L in content[8].split(',')]
    all_s = [int(L) for L in content[3].split(',')]
    all_x = [int(L) for L in content[4].split(',')]
    all_y = [int(L) for L in content[5].split(',')]
    x = [float(L) for L in content[9].split(',')]
    y = [float(L) for L in content[10].split(',')]

reconstructor_x = [L.strip()[1:-1] for L in content[11].split(';')]
reconstructor_y = [L.strip()[1:-1] for L in content[12].split(';')]
for i in range(len(reconstructor_x)):
    try:
        reconstructor_x[i] = [int(L) for L in reconstructor_x[i].split(',')]
        reconstructor_y[i] = [int(L) for L in reconstructor_y[i].split(',')]
    except:
        pass

N = n + 1

ITEMS = list(range(n))
NODES = list(range(N))
COURIERS = list(range(m))

D = np.array([[0 for j in range(N)] for i in range(N)])

for i in range(N):
    for j in range(N):
        D[i, j] = abs(x[i] - x[j]) + abs(y[i] - y[j])

model = cp_model.CpModel()

# VARIABLES
table = []
for k in COURIERS:
    rows = []
    for i in NODES:
        cols = []
        for j in NODES:
            cols.append(model.NewBoolVar(name=f't[{k},{i},{j}]'))
        rows.append(cols)
    table.append(rows)


#successor = [model.NewIntVar(0, N-1, 'successor%i' % i) for i in NODES]
#courier = [model.NewIntVar(0, N-1, 'courier%i' % i) for i in NODES]

# ------ initialization constraints ----

# Ongi oggetto raggiunto esattamente una volta
for i in ITEMS:
    model.AddExactlyOne([table[k][i][j] for k in COURIERS for j in NODES if j != i])
    model.AddExactlyOne([table[k][j][i] for k in COURIERS for j in NODES if j != i])

for k in COURIERS:
    model.Add(table[k][N-1][N-1] == 0)

"""
for k in COURIERS:
    somma = 0
    for j in range(N-1):
        somma += sum([table[k][i][j] for i in NODES if i != j])*s[j]
    model.Add(somma <= l[k])
"""

for k in COURIERS:
    model.Add(sum([table[k][i][j]*s[j] for i in NODES for j in range(N-1) if i != j]) <= l[k])

"""
ListOfItems = []
for k in range(m):
    objects = []
    for i in range(n):
        objects.append(model.NewBoolVar(name=f'O[{k},{i}]'))
    ListOfItems.append(objects)

for k in COURIERS:
    for i in ITEMS:
        model.Add(ListOfItems[k][i] == sum([table[k][i][j] for j in range(n)]))

# TEST - Symmetry Breaking
for k in COURIERS:
    for kk in range(k+1, m):
        if l[k] == l[kk]:
            model.Add(sum([ListOfItems[k][j]*j for j in ITEMS]) < sum([ListOfItems[kk][j]*j for j in ITEMS]))
"""

for k in COURIERS:
    arcs = []
    for i in NODES:
        for j in NODES:
            arcs.append((i, j, table[k][i][j]))
    model.AddCircuit(arcs)



obj = cp_model.LinearExpr.Sum([table[k][i][j]*D[i, j] for k in COURIERS for i in NODES for j in NODES])
model.Add(obj >= lower_boud)

model.Minimize(obj)
solver = cp_model.CpSolver()
# Massimo 5 minuti
solver.parameters.max_time_in_seconds = 300.0
status = solver.Solve(model)


if status == cp_model.OPTIMAL or status == cp_model.FEASIBLE:
    """
    for k in COURIERS:
        print(f"\nCourier{k}:\n")
        for i in NODES:
            for j in NODES:
                print(f'{solver.Value(table[k][i][j])}', end=" ")
            print("")
        print("--------------------------------------")
    """
    print(f'Minimum of objective function: {solver.ObjectiveValue()}\n')
    pre_optimization = {solver.ObjectiveValue()}
    for k in COURIERS:
        somma = 0
        for j in range(N-1):
            somma += sum([solver.Value(table[k][i][j]) for i in NODES if i != j])*s[j]
        print("sum[{}] = {} and l[{}] = {}".format(k, somma, k, l[k]))


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
    if semplification:
        post_optimization = 0
        print("INIZIO OTIMMIZAZIONE FINALE")
        who_have_what = [[] for k in range(m)]
        for k in range(m):
            for i in range(N):
                for j in range(N):
                    if solver.Value(table[k][i][j]) == 1 and i != j:
                        who_have_what[k].append(i)
        x_for_each = [[] for k in range(m)]
        y_for_each = [[] for k in range(m)]
        print(who_have_what)
        for k in range(m):
            for i in range(len(who_have_what[k])):
                for ii in range(len(reconstructor_x[who_have_what[k][i]])):
                    x_for_each[k].append(reconstructor_x[who_have_what[k][i]][ii])
                    y_for_each[k].append(reconstructor_y[who_have_what[k][i]][ii])
        print(x_for_each)
        color_i = 1
        color = 'C1'
        for k in range(m):
            N_opt = len(x_for_each[k])
            D = np.array([[0 for j in range(N_opt)] for i in range(N_opt)])
            for i in range(N_opt):
                for j in range(N_opt):
                    D[i, j] = abs(x_for_each[k][i] - x_for_each[k][j]) + abs(y_for_each[k][i] - y_for_each[k][j])

            #------------------------------------------------------------------------
            ITEMS = list(range(N_opt-1))
            NODES = list(range(N_opt))
            model = cp_model.CpModel()
            # VARIABLES
            table = []
            table.clear()
            for i in NODES:
                cols = []
                for j in NODES:
                    cols.append(model.NewBoolVar(name=f't[{i},{j}]'))
                table.append(cols)

            for i in ITEMS:
                model.AddExactlyOne([table[i][j] for j in NODES if j != i])
                model.AddExactlyOne([table[j][i] for j in NODES if j != i])

            model.Add(table[N_opt-1][N_opt-1] == 0)

            arcs = []
            for i in NODES:
                for j in NODES:
                    arcs.append((i, j, table[i][j]))
            model.AddCircuit(arcs)

            obj = cp_model.LinearExpr.Sum([table[i][j]*D[i, j] for i in NODES for j in NODES])

            model.Minimize(obj)
            solver = cp_model.CpSolver()
            solver.parameters.max_time_in_seconds = 20.0
            status = solver.Solve(model)

            #--------------------------------------------------------------------

            print(f"Done optimization for {k}-courier")
            print(f"N_opt {N_opt}")
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
            print("----------------------------------")
        print(f"{file}-OR-TOOLS Pre optimization: {pre_optimization}")
        print(f"{file}-OR-TOOLS Post optimization: {post_optimization}")
        plt.xlim(min(all_x)-2,max(all_x)+2)
        plt.ylim(min(all_y)-2,max(all_y)+2)
        plt.savefig(f'Results/Or_Tools/Or_tools_{file}.png')
        plt.clf()
else:
    print('No solution found.')

"""
plt.scatter(x[:-1], y[:-1], c='b')
for i in range(n):
    plt.annotate(f'q{i}', (x[i]+0.05, y[i]+0.05))

for k in COURIERS:
    for i in NODES:
        for j in NODES:
            if solver.Value(table[k][i][j]) == 1:
                plt.plot([x[i], x[j]], [y[i], y[j]], c='y', alpha=0.4)

plt.plot(x[-1], y[-1], c='r', marker='s')
plt.show()
"""
