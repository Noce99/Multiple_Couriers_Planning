#!/usr/bin/env python3.7

# Copyright 2022, Gurobi Optimization, LLC

# This example formulates and solves the following simple MIP model
# using the matrix API:
#  maximize
#        x +   y + 2 z
#  subject to
#        x + 2 y + 3 z <= 4
#        x +   y       >= 1
#        x, y, z binary

import gurobipy as gp
from gurobipy import GRB
import numpy as np
import scipy.sparse as sp

    # Create a new model
    m = gp.Model("matrix1")

    # Create variables
    x = m.addMVar(shape=(3, 3), vtype=GRB.BINARY, name="x")
    
    # Set objective
    obj = np.array([1.0, 1.0, 2.0])
    obj2 = np.array([[1.0], [1.0], [2.0]])
    print(obj.shape)
    print(x.shape)
    print(obj2.shape)
    print(obj @ x @ obj2)
    m.setObjective(1, GRB.MAXIMIZE)

    # Optimize model
    m.optimize()

    print(x.X)
    print('Obj: %g' % m.ObjVal)
