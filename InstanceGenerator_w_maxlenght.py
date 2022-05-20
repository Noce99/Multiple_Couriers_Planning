# UPLOAD ALL THE INSTANCES IN THE 'Inst' FOLDER, THEN RUN THIS PROGRAM.

import numpy as np
import os
import math

def binary_number_with_N_digits(N):
    NUM_OF_INT = 1
    for i in range(N):
        NUM_OF_INT += 2**i
    binary_list = np.zeros(shape=(NUM_OF_INT, N), dtype=int)
    for i in range(1, NUM_OF_INT):
        if binary_list[i-1][0] == 1:
            carry = 1
            binary_list[i][0] = 0
        else:
            binary_list[i][0] = 1
            carry = 0
        for j in range(1, N):
            if binary_list[i-1][j] == 0:
                if carry == 0:
                    binary_list[i][j] = 0
                else:
                    binary_list[i][j] = 1
                    carry = 0
            else:
                if carry == 0:
                    binary_list[i][j] = 1
                else:
                    binary_list[i][j] = 0
                    carry = 1
    return binary_list


os.mkdir('mcp_inst')

for file in os.listdir("Inst/"):

  # Reading the file
  f = open('Inst/' + file, "r")
  text = f.read()
  f.close()

  # Splitting the file by rows
  content = text.split('\n')

  # Number of objects to deliver
  n = int(content[1])
  m = int(content[0])

  # Delivery coordinates of each object
  x = [int(el) for el in content[4].split(' ')]
  y = [int(el) for el in content[5].split(' ')]

  # Intantiating the distance matrix
  dist = np.zeros(shape=(n+1,n+1), dtype=int)

  # Filling the matrix with the Manhattan distance between each pair of objects
  for i in range(n+1):
    for j in range(i, n+1):
      dist[i, j] = dist[j, i] = abs(x[i] - x[j]) + abs(y[i] - y[j])

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

  # Creating a file in the new folder
  f = open('mcp_inst/' + file + '.dzn', "w")

  # Writing the new file .dzn of the instance
  f.write('m = ' + content[0] + ';\n')
  f.write('n = ' + content[1] + ';\n')
  f.write('l = ['); f.writelines([str(L) + ', ' for L in l]); f.write('];\n')
  f.write('s = ['); f.writelines([str(int(L)) + ', ' for L in content[3].split(' ')]); f.write('];\n')
  f.write('w = ['); f.writelines([str(L) + ', ' for L in w]); f.write('];\n')
  f.write('length = ['); f.writelines([str(L) + ', ' for L in length]); f.write('];\n')
  f.write('max_length = ' + str(max(length)) + ';\n')

  # Writing the matrix values in the file
  f.write('D = [|')
  for i in range(n+1):
    for j in range(n+1):
      f.write(str(dist[i, j]) + ', ')
    f.write('|')
  f.write('];\n')

  # Writing all reverse raw combination matrix
  binary_list = binary_number_with_N_digits(m)
  f.write('num_raw_combination = ' + str(len(binary_list)) + ';\n')
  f.write('raw_combination = [|')
  for i in range(len(binary_list)):
    for j in range(m):
      f.write(str(binary_list[i, j]) + ', ')
    f.write('|')
  f.write('];\n')

  # Closing the new file
  f.close()
