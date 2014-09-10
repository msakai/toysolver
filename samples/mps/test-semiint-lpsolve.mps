* Converted from Example 2 of http://lpsolve.sourceforge.net/5.5/Xpress-format.htm
* SCIP-2.1.1 and Gurobi-5.6.3 do not support 'SI' bound
NAME example2.lpx
ROWS
 N  OBJ     
 L  c1      
 L  c2      
COLUMNS
    MARK0000  'MARKER'                 'INTORG'
    x3        OBJ       -2
    x3        c2        1
    MARK0001  'MARKER'                 'INTEND'
    x2        c1        1
    x2        c2        1
    MARK0002  'MARKER'                 'INTORG'
    x1        c1        -1
    x1        c2        1
    MARK0003  'MARKER'                 'INTEND'
RHS
    RHS       c1        10
    RHS       c2        20
BOUNDS
 LO BND       x3        2
 SI BND       x3        3
 LO BND       x1        2.1
 SI BND       x1        30
ENDATA
