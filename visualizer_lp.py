
"""
Esempio:
1 2 2 4 5 5 6 3
3 1 5 0 2 5 4 3
NON TOCCARE SOPRA QUESTA LINEA
[[[0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0],[0,0,0,0,1,0,0,0],[0,0,0,1,0,0,0,0],[0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0],[1,0,0,0,0,0,0,0],],[[0,0,1,0,0,0,0,0],[0,0,0,0,0,0,0,0],[1,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0],],[[0,1,0,0,0,0,0,0],[1,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0],[0,0,0,0,0,0,1,0],[0,0,0,0,0,1,0,0],[0,0,0,0,0,0,0,0],],]
"""
import cv2
import numpy as np
import matplotlib.pyplot as plt

matrix = np.array(
[[[0,0,0,0,0,0,0,0],[0,0,0,1,0,0,0,0],[0,0,0,0,0,0,0,0],[0,0,0,0,1,0,0,0],[0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0],[0,1,0,0,0,0,0,0],],[[0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0],[0,0,0,0,0,1,0,0],[0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,0],[0,0,1,0,0,0,0,0],],[[0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0],[1,0,0,0,0,0,0,0],[0,0,0,0,0,0,1,0],],]
)
print(matrix)


lines = []
with open('input_visualizer.txt') as f:
    lines = f.readlines()
lines[0] = [int(el) for el in lines[0].split(' ')]
lines[1] = [int(el) for el in lines[1].split(' ')]


x = lines[0]
y = lines[1]

if min(x) < 0:
    x = np.array(x) - min(x)
    y = np.array(y) - min(y)

max_dim = max(max(x), max(y))
map = np.ones(shape=(max_dim, max_dim))*255

# Creating POINTS on the map
for i in range(len(x)):
    plt.gca().add_patch(plt.Circle((x[i],y[i]), 0.1, color='r'))

x1s = []
y1s = []
x2s = []
y2s = []
color_i = 1
color = 'C1'
for k in range(matrix.shape[0]):
    da, a = np.nonzero(matrix[k, :, :])
    x1s.clear()
    y1s.clear()
    x2s.clear()
    y2s.clear()
    for i in range(da.size):
        start = da[i]
        end = a[i]
        x1s.append(x[start])
        y1s.append(y[start])
        x2s.append(x[end]-x[start])
        y2s.append(y[end]-y[start])
    plt.quiver(x1s, y1s, x2s, y2s, angles='xy', scale_units='xy', color=[color], scale=1, width=0.001)
    color_i += 1
    color = 'C'+str(color_i)

"""
start = len(x)-1
current = start
next = succesor[start] - 1
x1s = []
y1s = []
x2s = []
y2s = []
# print("start: ", start)
# print("next: ", next)
color_i = 1
color = 'C1'
while next != start:
    if current <=  len(x)-1:
        wcurrent = current
    else:
        wcurrent = len(x)-1
        color_i += 1
        color = 'C'+str(color_i)
        plt.quiver(x1s, y1s, x2s, y2s, angles='xy', scale_units='xy', color=[color], scale=1, width=0.001)
        x1s.clear()
        y1s.clear()
        x2s.clear()
        y2s.clear()
    if next <=  len(x)-1:
        wnext = next
    else:
        wnext = len(x)-1
    x1s.append(x[wcurrent])
    y1s.append(y[wcurrent])
    x2s.append(x[wnext]-x[wcurrent])
    y2s.append(y[wnext]-y[wcurrent])
    # print((x[current], y[current], x[next], y[next]))
    # plt.plot(x[current], y[current], x[next], y[next], marker = 'o')
    current = next
    next = succesor[next] - 1
    # print("current: ", current)
    # print("next: ", next)
color_i += 1
color = 'C'+str(color_i)
plt.quiver(x1s, y1s, x2s, y2s, angles='xy', scale_units='xy', color=[color], scale=1, width=0.001)
"""
plt.xlim(min(x)-2,max(x)+2)
plt.ylim(min(y)-2,max(y)+2)
plt.show()
