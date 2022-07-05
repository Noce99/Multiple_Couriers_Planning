from docplex.mp.model import *
import numpy as np
import scipy.sparse as sp
import matplotlib.pyplot as plt

rnd = np.random
rnd.seed(0)

lines = []
with open('Inst/inst01') as f:
    lines = f.readlines()

m = int(lines[0])   
n = int(lines[1])  
l = [int(el) for el in lines[2].split(' ')]
s = [int(el) for el in lines[3].split(' ')]
x = [int(el) for el in lines[4].split(' ')]
y = [int(el) for el in lines[5].split(' ')]

N = n + 1

plt.scatter(x, y)
for i in range(n):
    plt.annotate(f'q{i}', (x[i]+0.05, y[i]+0.05))
plt.annotate(f'Depot', (x[-1]+0.05, y[-1]+0.05))
plt.show()


Arcs = [(i, j, k) for i in range(N) for j in range(N) for k in range(m)]
#Dist = {(i, j):round(np.sqrt((x[i]-x[j])**2 + (y[i]-y[j])**2)) for i in range(N) for j in range(N)}
Dist = {(i, j):np.sum([abs(x[i]-x[j]), abs(y[i]-y[j])]) for i in range(N) for j in range(N)}

mdl = Model('MCP')

table = mdl.binary_var_dict(Arcs, name='table')
order = mdl.integer_var_dict([i for i in range(N)], lb=0, ub=n, name='order')

# OBJECTIVE FUNCTION
mdl.minimize(mdl.sum(Dist[i, j]*table[i, j, k] for i in range(N) for j in range(N) for k in range(m)))

# CONSTRAINTS

# DIAGONAL -> ZEROS
mdl.add_constraint(mdl.sum(table[i, i, k] for i in range(n) for k in range(m)) == 0)

#mdl.add_constraints(mdl.sum(table[i, j, k] - table[j, i, k] for i in range(N)) == 0 for j in range(N) for k in range(m))

for i in range(N):
    for k in range(m):
        mdl.add_constraint(mdl.sum(table[i, j, k] for j in range(N)) == mdl.sum(table[j, i, k] for j in range(N)))

# ALL OBJECTS
for i in range(n):
    mdl.add_constraint(mdl.sum(table[i, j, k] for j in range(N) for k in range(m)) == 1)
    mdl.add_constraint(mdl.sum(table[j, i, k] for j in range(N) for k in range(m)) == 1)

# ALL STARTS FROM THE DEPOT
for k in range(m):
    mdl.add_constraint(mdl.sum(table[N-1, j, k] for j in range(n)) == 1)
    mdl.add_constraint(mdl.sum(table[j, N-1, k] for j in range(n)) == 1)

# CHECK ON WEIGHTS
for k in range(m):
    mdl.add_constraint(mdl.sum(table[i, j, k]*s[j] for i in range(N) for j in range(n)) <= l[k])

# REMOVE SUBTOURS
for i in range(N):
    for j in range(N-1):
        for k in range(m):
            mdl.add_constraint(order[N-1] == 1)
            mdl.add_constraint(order[i]-order[j]+1 <= (N-2)*(1-table[i, j, k]))


# TIME LIMIT
mdl.time_limit = 300
solution = mdl.solve(log_output=True)


# PLOT
tour = [arc for arc in Arcs if table[arc].solution_value>0.9]

plt.scatter(x[:-1], y[:-1], c='b')
for i in range(n):
    plt.annotate(f'q{i}', (x[i]+0.05, y[i]+0.05))

for i, j, k in tour:
    plt.plot([x[i], x[j]], [y[i], y[j]], c='y', alpha=0.4)
    
plt.plot(x[-1], y[-1], c='r', marker='s')
plt.show()