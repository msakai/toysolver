\ http://www.gurobi.com/documentation/5.0/reference-manual/node746
\ Gurobi 5.0.1: Ok
\ SCIP 2.1.1: error

Maximize
  x + y + z
Subject To
  c0: x + y = 1
  c1: x + 5 y + 2 z <= 10
  qc0: x + y + [ x ^ 2 - 2 x * y + 3 y ^ 2 ] <= 5
Bounds
  0 <= x <= 5
  z >= 2
Generals
  x y z
End
