* http://pic.dhe.ibm.com/infocenter/cosinfoc/v12r4/topic/ilog.odms.cplex.help/CPLEX/File_formats_reference/topics/MPS_ext_indicators.html
NAME          ind1.mps
ROWS
 N  obj
 L  row2
 L  row4
 E  row1
 E  row3
COLUMNS
    x         obj                            -1
    x         row2                            1
    x         row4                            1
    x         row1                            1
    y         row4                            1
    z         row4                            1
    z         row3                            1
RHS
    rhs       row2                           10
    rhs       row4                           15
BOUNDS
 UI bnd       y                               1
INDICATORS
 IF row1      y                               1
 IF row3      y                               0
ENDATA
