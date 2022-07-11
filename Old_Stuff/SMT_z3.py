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

f = open("MCP_SMT.smt2", "w")
[[[f.write("(declare-const table_{}_{}_{} Bool)\n".format(k, i, j)) for j in range(n)] for i in range(n)] for k in range(m)]

# Un pacco alla volta per passo
for k in range(m):
    for i in range(n):
        for j in range(n):
            f.write("(assert (or (not table_{}_{}_{}) (and ".format(k, j, i))
            for jj in range(n):
                if jj != j:
                    f.write("(not table_{}_{}_{}) ".format(k, jj, i))
            f.write(")))\n")

for k in range(m):
    for i in range(n):
        for j in range(n):
            f.write("(assert (or (not table_{}_{}_{}) (and ".format(k, j, i))
            for kk in range(m):    
                for ii in range(n):
                    if ii != i or k != kk:
                        f.write("(not table_{}_{}_{}) ".format(kk, j, ii))
            f.write(")))\n")
            
for i in range(n):
    f.write("(assert (or ")
    for k in range(m):
        for j in range(n):
            f.write("table_{}_{}_{} ".format(k, i, j))
    f.write("))\n")

for k in range(m):
    f.write("(assert (or ")
    for i in range(n):
        for j in range(n):
            f.write("table_{}_{}_{} ".format(k, i, j))
    f.write("))\n") 
        
f.write("(check-sat)\n(get-model)")
f.close()

print("Let's try to solve it:")
output = ""
with tempfile.TemporaryFile() as tempf:
    proc = subprocess.Popen(["z3", "-smt2", "MCP_SMT.smt2"], stdout=tempf)
    proc.wait()
    tempf.seek(0)
    output = tempf.read().decode("utf-8")
content = output.split('\n')
print(content)
print("------------------------------------------------------------------------")
print("RESULT: {}".format(content[0]))
content.pop(0)
content.pop(0)
content.pop()
content.pop()
content_copy = content.copy()
for i in range(len(content_copy), -1, 1):
    if len(content_copy[i]) < 2:
        content.pop(i)
for i in range(len(content)):
    content[i] = content[i][4:]
for i in range(len(content)):
    if len(content[i]) > 6:
        content[i] = content[i][16:-8].split('_')
        content[i][0] = int(content[i][0])
        content[i][1] = int(content[i][1])
        content[i][2] = int(content[i][2])
    else:
        content[i] = content[i][:-1]
        if content[i] == 'false':
            content[i] = 0
        else:
            content[i] = 1
table = [[[2 for j in range(n)] for i in range(n)] for k in range(m)]
for i in range(len(content), 0, -2):
    value = content.pop()
    position = content.pop()
    table[position[0]][position[1]][position[2]] = value

for k in range(m):
    print("Tizio {}".format(k+1))
    for i in range(n):    
        print(table[k][i])
    print("\n")
    
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
    for i in range(n):
        for j in range(n):
            if table[k][j][i] > 0:
                if last == -1:
                    x1s.append(x[n])
                    y1s.append(y[n])
                    x2s.append(x[j]-x[n])
                    y2s.append(y[j]-y[n])
                    last = j
                else:
                    x1s.append(x[last])
                    y1s.append(y[last])
                    x2s.append(x[j]-x[last])
                    y2s.append(y[j]-y[last])
                    last = j
    x1s.append(x[last])
    y1s.append(y[last])
    x2s.append(x[n]-x[last])
    y2s.append(y[n]-y[last])
    plt.quiver(x1s, y1s, x2s, y2s, angles='xy', scale_units='xy', color=[color], scale=1, width=0.003)
    color_i += 1
    color = 'C'+str(color_i)
plt.xlim(min(x)-2,max(x)+2)
plt.ylim(min(y)-2,max(y)+2)
plt.show()
