\ GLPK: parser error
\ Gurobi: 2.5 is recognized as variable!
\ CPLEX: 2.5 is ignored, and warned.

\ gurobi> m.getObjective()
\ <gurobi.LinExpr: 1.0 x1 + 2.0 x2 + 3.0 x3 + 1.0 x4 + 1.0 2.5>
\ gurobi> m.getVars()
\ [<gurobi.Var x1>, <gurobi.Var x2>, <gurobi.Var x3>, <gurobi.Var x4>, <gurobi.Var
2.5>]

Maximize
obj: x1 + 2 x2 + 3 x3 + x4 + 2.5
Subject To
c1: - x1 + x2 + x3 + 10 x4 <= 20
c2: x1 - 3 x2 + x3 <= 30
c3: x2 - 3.5 x4 = 0
Bounds
0 <= x1 <= 40
2 <= x4 <= 3
General
x4
End
