0.5.0
-----
* pbconvert and lpconvert were merged into a single command 'toyconvert'.

0.4.0
-----
* add experimental SMT (Satisfiablity Modulo Theories) solver 'toysmt', which supports theory of uninterpreted functions and linear real arithmetics.
* fix toysat to output model in Max-SAT format instead of PB/WBO format when solving Max-SAT problems
* add experimental getAssumptionsImplications functions to ToySolver.SAT module.
* add getFixedLiterals to ToySolver.SAT module.
* use 'mwc-random' package instead of 'random' package.
* introduce 'Config' data type in ToySolver.SAT to simplify configulation management.
* add subset-sum problem solver
* implement backracking and explanation generation in simplex solver and congruence closure solver.

0.3.0
-----
* split OPB/WBO file library into a serarate 'pseudo-boolean' library.

