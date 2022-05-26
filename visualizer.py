
"""
Esempio:
-30 -31 52 -13 -67 49 5 -65 -4 23 25 -43 -77 -21 -52 -41 -92 -65 19 -41 -38 24 -43 -35 -55 -49 57 -23 -57 -39 -17 -12 -47 16 1 -26 4 -51 -23 -71 -8 12 -19 -12 30 12 -38 -10
64 5 5 69 68 6 22 77 -2 12 6 -26 99 58 7 51 28 30 97 83 -33 29 20 -25 14 33 24 55 73 -4 20 12 98 9 7 30 15 -23 -10 -19 32 -25 -24 12 12 -56 -22 20
NON TOCCARE SOPRA QUESTA LINEA
[28, 30, 6, 14, 18, 45, 17, 25, 7, 55, 4, 26, 53, 40, 33, 29, 20, 24, 12, 19, 16, 3, 34, 27, 9, 13, 10, 8, 1, 37, 44, 46, 22, 15, 39, 54, 36, 5, 43, 47, 31, 52, 41, 11, 42, 23, 2, 32, 21, 35, 38, 49, 50, 51, 48]
[2, 3, 1, 3, 4, 1, 2, 2, 2, 4, 3, 2, 2, 3, 1, 2, 2, 4, 2, 2, 2, 1, 1, 4, 2, 2, 4, 2, 2, 3, 3, 1, 1, 1, 3, 3, 3, 4, 3, 3, 3, 1, 3, 3, 1, 1, 3, 1, 2, 3, 4, 1, 2, 3, 4]
[183, 196, 171, 97]
717
"""
import cv2
import numpy as np
import matplotlib.pyplot as plt

lines = []
with open('input_visualizer.txt') as f:
    lines = f.readlines()
lines[0] = [int(el) for el in lines[0].split(' ')]
lines[1] = [int(el) for el in lines[1].split(' ')]
lines[3] = lines[3][1:]
lines[3] = lines[3][:-2]
lines[3] = [int(el) for el in lines[3].split(', ')]
lines[4] = lines[4][1:]
lines[4] = lines[4][:-2]
lines[4] = [int(el) for el in lines[4].split(', ')]


x = lines[0]
y = lines[1]
succesor = lines[3]
couriers = lines[4]

if min(x) < 0:
    x = np.array(x) - min(x)
    y = np.array(y) - min(y)

max_dim = max(max(x), max(y))
map = np.ones(shape=(max_dim, max_dim))*255

# Creating POINTS on the map
for i in range(len(x)):
    plt.gca().add_patch(plt.Circle((x[i],y[i]), 0.1, color='r'))


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
plt.xlim(min(x)-2,max(x)+2)
plt.ylim(min(y)-2,max(y)+2)
plt.show()
