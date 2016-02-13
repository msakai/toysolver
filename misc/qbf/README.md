Toyqbf submission for the QBFEVAL'16
====================================

Usage
-----

    ./toyqbf +RTS -H1G -K1G -RTS file.cnf
    ./toyqbf +RTS -H1G -K1G -RTS file.qdimacs

Algorithm
---------

We have implemented Counterexample Guided Refinement algorithm for QBF [1] on
top on our own CDCL SAT solver 'toysat'.

Source Code
-----------

The source code is available from <https://github.com/msakai/toysolver>.

License
-------

This program is licenced under the BSD-style license.
(See the file 'COPYING'.)

References
----------

* [1] Mikoláš Janota, William Klieber, Joao Marques-Silva, Edmund Clarke.
  Solving QBF with Counterexample Guided Refinement.
  In Theory and Applications of Satisfiability Testing (SAT 2012), pp. 114-128.
  <http://dx.doi.org/10.1007/978-3-642-31612-8_10>
  <https://www.cs.cmu.edu/~wklieber/papers/qbf-cegar-sat-2012.pdf>
