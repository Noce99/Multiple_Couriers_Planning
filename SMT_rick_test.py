import numpy as np
import matplotlib.pyplot as plt
import sys
import time
import subprocess
import tempfile

if len(sys.argv) < 2:
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
s = [int(L) for L in content[3].split(',')]
x = [int(L) for L in content[4].split(',')]
y = [int(L) for L in content[5].split(',')]  
     
N = n + 1

lines = []
f = open("MCP_SMT_rick.smt2", "w")

lines.append("(declare-fun table (Int Int Int) Bool)")


# Ogni corriere deve partire (xor last row)
for k in range(m):
    lines += [f"(assert (xor {' '.join([f'(= (select table {k} {n-1} {j}) 1)' for j in range(n)])}))"]

# Ogni corriere deve tornare (xor last column)
for k in range(m):
    lines += [f"(assert (xor {' '.join([f'(= (select table {k} {i} {n-1}) 1)' for i in range(n)])}))"]

# Un 1 per ogni riga
for i in range(n):
    lines += [f"(assert (xor {' '.join([f'(= (select table {k} {i} {j}) 1)' for k in range(m) for j in range(n)])}))"]

# Un 1 per ogni colonna
for j in range(n):
    lines += [f"(assert (xor {' '.join([f'(= (select table {k} {i} {j}) 1)' for k in range(m) for i in range(n)])}))"]


# Edge (i, j) = 1 -> (xor in row j)
for k in range(m):
    for i in range(n):
        for j in range(n):
            lines += [f"(assert (or (not (select table {k} {i} {j})) (xor {' '.join([f'(= (select table {k} {j} {jj}) 1)' for jj in range(n)])})))"]


f.write(lines)
f.close()