# UPLOAD ALL THE INSTANCES IN THE 'Inst' FOLDER, THEN RUN THIS PROGRAM.

import numpy as np
import os

os.mkdir('new_inst')

for file in os.listdir("./Inst"):

  # Reading the file
  f = open('Inst/' + file, "r")
  text = f.read()
  f.close()

  # Splitting the file by rows
  content = text.split('\n')

  # Number of items to be delivered
  n = int(content[1])
  
  # Delivery coordinates of each object
  x = [int(el) for el in content[4].split(' ')]
  y = [int(el) for el in content[5].split(' ')]

  # Intantiating the distance matrix
  dist = np.zeros(shape=(n,n), dtype=int)

  # Filling the matrix with the Manhattan distance between each pair of objects
  for i in range(n):
    for j in range(i, n):
      dist[i, j] = dist[j, i] = abs(x[i] - x[j]) + abs(y[i] - y[j])

  # Creating a file in the new folder
  f = open('new_inst/' + file + '.dzn', "w")

  # Writing the new file .dzn of the instance
  f.write('n = ' + content[0] + ';\n')
  f.write('m = ' + content[1] + ';\n')
  f.write('l = [| '); f.writelines([L for L in content[2]]); f.write(' |];\n')
  f.write('s = [| '); f.writelines([L for L in content[3]]); f.write(' |];\n')
  
  # Writing the matrix values in the file
  f.write('D = [| ') 
  for i in range(n):
    for j in range(n):
      f.write(str(dist[i, j]) + ' ')
    f.write('|\n')
  f.write('];\n')

  # Closing the new file
  f.close()
