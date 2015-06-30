Toysat submission for the Pseudo-Boolean Evaluation 2015
========================================================

Usage
-----

    ./toysat +RTS -H1G -K1G -RTS --search=bcd2 file.opb

About Solver Requirments and Optional Features
----------------------------------------------

Minimum Requirments

* solve decision problems: YES
* handle 32 bit Integers: YES
* handle cardinality constraints: YES

Optional Features

* solve optimization problems: YES
    * incomplete optimization: 
    * complete optimization: ✓
* handle 64 bit Integers: YES (it can handle arbitrary integers)
* handle general pseudo-Boolean constraints: YES

Algorithm
---------

We have implemented BCD2 algorithm [1] on top on our own CDCL SAT solver
'toysat' with watch-literal based cardinality constraint handler and
counter-based linear pseudo boolean constraint handler. One of the major
difference from the original BCD2 is that our implementation uses incremental
solving features of SAT solver to keep the information such as learnt clauses
in the successive invocations of SAT solver.

Non-linear constraints and objective functions are handled by linearization
using a variant of Tseitin transformation that take the polarity into account
[2].

References
----------

* [1] A. Morgado, F. Heras, and J. Marques-Silva,
  Improvements to Core-Guided binary search for MaxSAT,
  in Theory and Applications of Satisfiability Testing (SAT 2012),
  pp. 284-297.
  <http://dx.doi.org/10.1007/978-3-642-31612-8_22>

* [2] N. Eén and N. Sörensson,
  Translating pseudo-boolean constraints into SAT, Journal on Satisfiability,
  Boolean Modeling and Computation, vol. 2, pp. 1-26, 2006.
