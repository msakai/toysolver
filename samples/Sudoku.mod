set Number := 1..9;

param Data{Number, Number, Number} binary default 0;

var Ans{Number, Number, Number} binary;
s.t. GIVEN{x in Number, y in Number, n in Number}: Data[x,y,n] <= Ans[x,y,n];
s.t. FILLED{x in Number, y in Number}: sum{n in Number} Ans[x,y,n] = 1;
s.t. COL{n in Number, x in Number}: sum{y in Number} Ans[x,y,n] = 1;
s.t. ROW{n in Number, y in Number}: sum{x in Number} Ans[x,y,n] = 1;
s.t. BLOCK{n in Number, x0 in 0..2, y0 in 0..2}:
      sum{x1 in 1..3, y1 in 1..3} Ans[3*x0+x1, 3*y0+y1, n] = 1;

