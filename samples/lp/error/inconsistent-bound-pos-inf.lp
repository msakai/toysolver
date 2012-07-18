\...
Maximize
 obj: x1 + 2 x2 + 3 x3 + x4
Subject To
 c1: - x1 + x2 + x3 + 10 x4 <= 20
 c2: x1 - 3 x2 + x3 <= 30
 c3: x2 - 3.5 x4 = 0
Bounds
 +inf <= x1 <= 40
 2 <= x4 <= 3
General
 x4
End

\ GLPK: samples/inconsistent-bound-inf.lp:9: invalid use of `+inf' as lower bound
\ Gurobi: Model is infeasible or unbounded
\ lpsolve: Error: bound contradicts earlier bounds on line 9
\ SCIP: infeasible
