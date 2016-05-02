Toysat submission for the Pseudo-Boolean Competition 2016
=========================================================

Usage
-----

    toysat +RTS -H1G -MMEMLIMITm -K1G -RTS --pb --search=bcd2 BENCHNAME

    toysat +RTS -H1G -MMEMLIMITm -K1G -RTS --wbo --search=bcd2 BENCHNAME

Categories of benchmarks
------------------------

* PB
  * DEC-BIGINT-LIN (no optimisation, big integers, linear constraints) 
  * DEC-BIGINT-NLC (no optimisation, big integers, non linear constraints) 
  * DEC-SMALLINT-LIN (no optimisation, small integers, linear constraints) 
  * DEC-SMALLINT-NLC (no optimisation, small integers, non linear constraints) 
  * DEC-SMALLINT-NLC (no optimisation, small integers, non linear constraints) 
  * OPT-BIGINT-LIN (optimisation, big integers, linear constraints) 
  * OPT-BIGINT-NLC (optimisation, big integers, non linear constraints) 
  * OPT-SMALLINT-LIN (optimisation, small integers, linear constraints) 
  * OPT-SMALLINT-NLC (optimisation, small integers, non linear constraints) 
* WBO
  * PARTIAL-BIGINT-LIN (both soft and hard constraints, big integers, linear constraints) 
  * PARTIAL-BIGINT-NLC (both soft and hard constraints, big integers, non linear constraints) 
  * PARTIAL-SMALLINT-LIN (both soft and hard constraints, small integers, linear constraints) 
  * PARTIAL-SMALLINT-NLC (both soft and hard constraints, small integers, non linear constraints) 
  * SOFT-BIGINT-LIN (only soft constraints, big integers, linear constraints) 
  * SOFT-BIGINT-NLC (only soft constraints, big integers, non linear constraints) 
  * SOFT-SMALLINT-LIN (only soft constraints, small integers, linear constraints) 
  * SOFT-SMALLINT-NLC (only soft constraints, small integers, non linear constraints) 

Algorithm
---------

We have implemented BCD2 algorithm [1] on top on our own CDCL SAT solver
'toysat' [2] with watch-literal based cardinality constraint handler and
counter-based linear pseudo boolean constraint handler. One of the major
difference from the original BCD2 is that our implementation uses incremental
solving features of SAT solver to keep the information such as learnt clauses
in the successive invocations of SAT solver.

Non-linear constraints and objective functions are handled by linearization
using a variant of Tseitin transformation that take the polarity into account
[3].

References
----------

* [1] A. Morgado, F. Heras, and J. Marques-Silva,
  Improvements to Core-Guided binary search for MaxSAT,
  in Theory and Applications of Satisfiability Testing (SAT 2012),
  pp. 284-297.
  <http://dx.doi.org/10.1007/978-3-642-31612-8_22>

* [2] Masahiro Sakai. <https://github.com/msakai/toysolver>

* [3] N. Eén and N. Sörensson,
  Translating pseudo-boolean constraints into SAT, Journal on Satisfiability,
  Boolean Modeling and Computation, vol. 2, pp. 1-26, 2006.
