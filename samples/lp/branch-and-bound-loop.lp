\ Integrating Simplex with DPLL(T)
\ by Bruno Dutertre and Leonardo de Moura
\ 
\ the constraint 1 <= 3x − 3y <= 2 is not satisfiable if x and y are
\ integers, but has unbounded real solutions. On this example, a naıve
\ branch-and-bound implementation loops.
\
\ Gurobi: OK
\ SCIP: OK
\ GLPK: loops

Minimize
  0 x
Subject To
  3 x - 3 y >= 1
  3 x - 3 y <= 2
Bounds
  -inf <= x <= +inf
  -inf <= y <= +inf
General
  x y
End
