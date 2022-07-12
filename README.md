# Multiple Couriers Planning
It has become very common nowadays, especially after the outbreak of the COVID-19 pandemic, to send or receive items online (food, goods, clothes, documents, . . . ). Hence, it is more and more important for companies to efficiently schedule the dispatching of items through different couriers, in order to minimize the transportation costs.    
   As the combinatorial decision and optimization expert, the student is assigned to solve the Multiple Couriers Planning (MCP) problem which is defined as follows. We have *m* couriers that must distribute *n ≥ m* items at different customer locations. Each courier *i* has a maximum *load size l<sub>i</sub>*. Each item *j* has a *distribution point d<sub>j</sub>* and a *size s<sub>j</sub>* (which can represent for instance a weight or a volume). The goal of MCP is to decide for each courier the items to be distributed and plan a *tour* (i.e. a sequence of location points to visit) to perform the necessary distribution tasks. Each courier tour must start and end at a given origin point *o*. Moreover, the maximum load li of the courier *i* should be respected when items are assigned to it. The objective is to minimize the total tour distance.
# Usage
## Or-Tools
First of all check that inside *instGen.py* we have *MAX_ITEM_NUM = 40*

      rm -r tsp_inst
      python instGen.py
      python or_tools_cp.py [1:11 number]
## Gurobi
First of all check that inside *instGen.py* we have *MAX_ITEM_NUM = 40*

      rm -r tsp_inst
      python instGen.py
      python lp_gurobi.py [1:11 number]
## SMT
First of all check that inside *instGen.py* we have *MAX_ITEM_NUM = 15*

      rm -r tsp_inst
      python instGen.py
      python SMT_Z3.py [1:11 number]