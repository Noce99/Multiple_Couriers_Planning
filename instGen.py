# UPLOAD ALL THE INSTANCES IN THE 'Inst' FOLDER, THEN RUN THIS PROGRAM.

import numpy as np
import os
import math
from math import sqrt

#PARAMETERS
MAX_ITEM_NUM = 40 # Put 15 for SMT

def prim(G):
  # Prim's Algorithm used to calculate the lower bound
  INF = 9999999
  V = G.shape[0]
  tot = 0
  selected = np.zeros(shape=(G.shape[0],))
  no_edge = 0
  selected[0] = True
  while (no_edge < V - 1):
      minimum = INF
      x = 0
      y = 0
      for i in range(V):
          if selected[i]:
              for j in range(V):
                  if ((not selected[j]) and G[i][j]):
                      if minimum > G[i][j]:
                          minimum = G[i][j]
                          x = i
                          y = j
      selected[y] = True
      tot += minimum
      no_edge += 1
  return tot
def unify_most_close_points(d, verbose=False):
    # Used to find out better point for aggregation
    global x
    global y
    global n
    global s
    global l
    global unifications_reconstructor_x
    global unifications_reconstructor_y
    max_l = max(l)
    min = (1, 0)
    for i in range(len(d)-1):
        for j in range(len(d[0])-1):
            if d[i][j] < d[min[0]][min[1]] and i != j and s[i]+s[j] < max_l:
                min = (i, j)
    new_x = (x[min[0]] + x[min[1]])/2.
    new_y = (y[min[0]] + y[min[1]])/2.
    for i in range(len(d)):
        d[min[1]][i] = sqrt((new_x - x[i])**2 + (new_y - y[i])**2)
    for i in range(len(d)):
        d[i][min[1]] = sqrt((new_x - x[i])**2 + (new_y - y[i])**2)
    d.pop(min[0])
    for i in range(len(d)):
        d[i].pop(min[0])
    x[min[1]] = new_x
    y[min[1]] = new_y
    x.pop(min[0])
    y.pop(min[0])
    unifications_reconstructor_x[min[1]] += unifications_reconstructor_x[min[0]]
    unifications_reconstructor_y[min[1]] += unifications_reconstructor_y[min[0]]
    unifications_reconstructor_x.pop(min[0])
    unifications_reconstructor_y.pop(min[0])
    n = n - 1
    s[min[1]] += s[min[0]]
    s.pop(min[0])
    return d


os.mkdir('tsp_inst')

for file in os.listdir("Inst/"):

  # Reading the file
  f = open('Inst/' + file, "r")
  text = f.read()
  f.close()

  # Splitting the file by rows
  content = text.split('\n')

  # Number of objects to deliver
  n = int(content[1])

  # Delivery coordinates of each object
  x = [int(el) for el in content[4].split(' ')]
  y = [int(el) for el in content[5].split(' ')]
  unifications_reconstructor_x = [[x[i]] for i in range(len(x))]
  unifications_reconstructor_y = [[y[i]] for i in range(len(y))]

  # Intantiating the distance matrix
  dist = np.zeros(shape=(n+1,n+1), dtype=int)

  # Filling the matrix with the Manhattan distance between each pair of objects
  for i in range(n+1):
    for j in range(i, n+1):
      dist[i, j] = dist[j, i] = sqrt((x[i] - x[j])**2 + (y[i] - y[j])**2)

  lst = list(dist[-1, :-1])
  min_deposit_dist = lst.pop(np.argmin(lst)) + lst.pop(np.argmin(lst))
  lower_bound = prim(dist[:-1, :-1]) + min_deposit_dist

  # Creating w (ordered s)
  w = [int(L) for L in content[3].split(' ')]
  w.sort()

  # Creating length
  l = [int(L) for L in content[2].split(' ')]
  l.sort()
  l.reverse()
  length = []
  for ll in l:
    sum = 0
    length_l = 0
    for ww in w:
      sum += ww
      if sum > ll:
        break
      length_l += 1
    length.append(length_l)

  capacity = l.copy()
  while len(w) > 0:
      obj = w.pop(0)
      for idx, c in enumerate(capacity):
          if c >= obj:
              capacity[idx] -= obj
              break

  min_couriers = np.sum(np.array(capacity) - np.array(l) != 0)

# tolgo momentaneante la riduzione dei min_couriers
# min_couriers = len(l)


  l = l[:min_couriers]
  length = length[:min_couriers]
  s = [int(L) for L in content[3].split(' ')]
  max_s = max(s)
  # Creating a file in the new folder
  f = open('tsp_inst/' + file + '.dzn', "w")

  # Writing the new file .dzn of the instance
  f.write('m = ' + str(min_couriers) + ';\n')
  f.write('n = ' + content[1] + ';\n')
  f.write('l = ['); f.writelines([str(L) + ', ' for L in l]); f.write('];\n')
  f.write('s = ['); f.writelines([str(int(L)) + ', ' for L in content[3].split(' ')]); f.write('];\n')
  f.write('x = ['); f.writelines([str(L) + ', ' for L in x]); f.write('];\n')
  f.write('y = ['); f.writelines([str(L) + ', ' for L in y]); f.write('];\n')
  #f.write('min_couriers = ' + str(min_couriers) + ';\n')
  f.write('% lower_bound = ' + str(lower_bound) + ';\n')
  #f.write('w = ['); f.writelines([str(L) + ', ' for L in w]); f.write('];\n')
  f.write('length = ['); f.writelines([str(L) + ', ' for L in length]); f.write('];\n')

  #CREATING THE SIMPLIFIED MODEL
  simpl_dist = [[0 for i in range(n+1)] for ii in range(n+1)]
  for i in range(n+1):
      for j in range(n+1):
          simpl_dist[i][j] = dist[i, j]
  i = 0
  while n > MAX_ITEM_NUM:
      simpl_dist = unify_most_close_points(simpl_dist)
      i += 1
  print(f"\"{file}\" simplified {i} times!")
  print(file, "DONE!")
  f.write(f'n = {n};\n')
  f.write(f"s = {s}\n")
  f.write(f"x = {x}\n")
  f.write(f"y = {y}\n")
  f.write(f"X = [")
  for e in unifications_reconstructor_x:
      f.write(f"{e}; ")
  f.write("]\n")
  f.write(f"Y = [")
  for e in unifications_reconstructor_y:
      f.write(f"{e}; ")
  f.write("]\n")
  f.write("\n")

  # Writing the matrix values in the file
  """
  f.write('D = [|')
  for i in range(n+1):
    for j in range(n+1):
      f.write(str(dist[i, j]) + ', ')
    f.write('|')
  f.write('];\n')
  """
  """
  if (file == "inst_banale"):
      for i in range(n+1):
          print([dist[i, j] for j in range(n+1)])
      print("\n")
  """
  # Closing the new file
  f.close()
