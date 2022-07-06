# UPLOAD ALL THE INSTANCES IN THE 'Inst' FOLDER, THEN RUN THIS PROGRAM.

import numpy as np
import os
import math

# Prim's Algorithm in Python
def prim(G):

  INF = 9999999
  # number of vertices in graph
  V = G.shape[0]

  tot = 0

  # create a array to track selected vertex
  # selected will become true otherwise false
  selected = np.zeros(shape=(G.shape[0],))
  # set number of edge to 0
  no_edge = 0
  # the number of egde in minimum spanning tree will be
  # always less than(V - 1), where V is number of vertices in
  # graph
  # choose 0th vertex and make it true
  selected[0] = True
  # print for edge and weight

  while (no_edge < V - 1):
      # For every vertex in the set S, find the all adjacent vertices
      #, calculate the distance from the vertex selected at step 1.
      # if the vertex is already in the set S, discard it otherwise
      # choose another vertex nearest to selected vertex  at step 1.
      minimum = INF
      x = 0
      y = 0
      for i in range(V):
          if selected[i]:
              for j in range(V):
                  if ((not selected[j]) and G[i][j]):
                      # not in selected and there is an edge
                      if minimum > G[i][j]:
                          minimum = G[i][j]
                          x = i
                          y = j

      selected[y] = True
      tot += minimum
      no_edge += 1

  return tot

def unify_most_close_points(d):
    min = (0, 0)
    for i in range(n+1):
        for j in range(n+1):
            if d[i][j] < d[min[0]][min[1]] and d[i][j] > 0:
                min = (i, j)
    print(f"Selected: {min}")
    print("Before:")
    for i in range(n+1):
        print(d[i])
    d.pop(min[0])
    for i in range(n+1):
        d[i].pop(min[0])
    print("After:")
    for i in range(n+1):
        print(d[i])



NUM_OF_SECTIONS = 100 # If cahnged change also the same constant inside "cluster_assigner_gurobi.py"
def get_angle_section(x, y):
    angle = math.atan2(y, x)
    section_size = 2*math.pi/NUM_OF_SECTIONS
    return int(angle / section_size)


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

  # Intantiating the distance matrix
  dist = np.zeros(shape=(n+1,n+1), dtype=int)

  # Filling the matrix with the Manhattan distance between each pair of objects
  for i in range(n+1):
    for j in range(i, n+1):
      dist[i, j] = dist[j, i] = abs(x[i] - x[j]) + abs(y[i] - y[j])

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
  l = l[:min_couriers]
  length = length[:min_couriers]

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
  NUM_OF_POINTS = 100
  simpl_dist = [[0 for i in range(n+1)] for ii in range(n+1)]
  for i in range(n+1):
      for j in range(n+1):
          simpl_dist[i][j] = dist[i, j]

  print(file, "DONE!")
  if file == "inst_banale":
    unify_most_close_points(simpl_dist)

  # Writing the matrix values in the file
  """
  f.write('D = [|')
  for i in range(n+1):
    for j in range(n+1):
      f.write(str(dist[i, j]) + ', ')
    f.write('|')
  f.write('];\n')
  """
  if (file == "inst_banale"):
      for i in range(n+1):
          print([dist[i, j] for j in range(n+1)])
      print("\n")
  # Closing the new file
  f.close()
