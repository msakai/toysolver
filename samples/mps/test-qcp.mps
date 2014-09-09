* converted from http://www.gurobi.com/documentation/5.0/reference-manual/node746
NAME    problem      
OBJSENSE
 MAX
ROWS
 N  obj1
 E  c0
 L  c1
 L  qc0
COLUMNS
    MARK0000  'MARKER'                 'INTORG'
    x         c0        1
    x         c1        1
    x         obj1      1
    x         qc0       1
    y         c0        1
    y         c1        5
    y         obj1      1
    y         qc0       1
    z         c1        2
    z         obj1      1
    MARK0001  'MARKER'                 'INTEND'
RHS
    rhs       c0        1
    rhs       c1        10
    rhs       qc0       5
BOUNDS
 LI bound     x         0
 UI bound     x         5
 LI bound     y         0
 PL bound     y
 LI bound     z         2
 PL bound     z
QCMATRIX   qc0
    x         x         1
    x         y         -1
    y         x         -1
    y         y         3
ENDATA
