toysat_ls
=========

Usage
-----

    ./toysat_ls [file.cnf|file.wcnf]

Algorithm
---------

We have implemented BCD2 algorithm [1] on top on our own CDCL SAT solver
'toysat' with watch-literal based cardinality constraint handler and
counter-based linear pseudo boolean constraint handler. One of the major
difference from the original BCD2 is that our implementation uses incremental
solving features of SAT solver to keep the information such as learnt clauses
in the successive invocations of SAT solver.

In addition to that, toysat_ls uses UBCSAT (ubcsat-beta-12-b18.tar.gz) [2] to
find compute initial solution quickly.

References
----------

* [1] A. Morgado, F. Heras, and J. Marques-Silva,
  Improvements to Core-Guided binary search for MaxSAT,
  in Theory and Applications of Satisfiability Testing (SAT 2012),
  pp. 284-297.
  <http://dx.doi.org/10.1007/978-3-642-31612-8_22>

* [2] D. Tompkins and H. Hoos, UBCSAT: An implementation and experimentation
  environment for SLS algorithms for SAT and MAX-SAT, in Theory and Applications
  of Satisfiability Testing (2004), Springer, 2005, pp. 306-320.
  <http://dx.doi.org/10.1007/11527695_24>
