\ http://lists.gnu.org/archive/html/help-glpk/2010-12/msg00055.html
\ From:    Andrew Makhorin
\ Subject: Re: [Help-glpk] Skip preprocessing
\ Date:	   Thu, 16 Dec 2010 15:16:23 +0300

\ Your instance has a property that lp relaxation to it has no finite
\ maximum while the integer feasible region is empty (in fact, 1/3 <= x1
\ - x2 <= 3/4, so no integers x1 and x2 can satisfy this constraint).

Maximize
  obj: x2
Subject To
  c1: 3 x1 - 3 x2 >= 1
  c2: 4 x1 - 4 x2 <= 3
Bounds 
  1 <= x1
  0 <= x2
General
  x1 x2
End
