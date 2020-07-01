toysat
======

Usage
-----

    ./toysat [file.cnf|file.wcnf]

Algorithm
---------

We have implemented BCD2 algorithm [1] on top on our own CDCL SAT solver
'toysat' with watch-literal based cardinality constraint handler and
counter-based linear pseudo boolean constraint handler. One of the major
difference from the original BCD2 is that our implementation uses incremental
solving features of SAT solver to keep the information such as learnt clauses
in the successive invocations of SAT solver.

References
----------

* [1] A. Morgado, F. Heras, and J. Marques-Silva,
  Improvements to Core-Guided binary search for MaxSAT,
  in Theory and Applications of Satisfiability Testing (SAT 2012),
  pp. 284-297.
  <https://doi.org/10.1007/978-3-642-31612-8_22>
