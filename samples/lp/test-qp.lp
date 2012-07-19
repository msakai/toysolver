\ GLPK: error
\ Gurobi 5.0.1: Ok
\ SCIP: okay? but "Quadratic constraint handler does not have LAPACK for eigenvalue computation. Will assume that matrices (with size > 2x2) are indefinite."
Minimize
obj: a + b + [ a^2 + 4 a * b + 7 b^2 ] / 2
Subject To
c1: a + b >= 10
End
