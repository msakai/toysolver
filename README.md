toysolver
=========

Installation
------------

* unpack
* cd toysolver
* cabal install

Usage
-----

This package includes several commands.

### toysolver

Arithmetic solver for the following problems:

* Mixed Integer Liner Programming (MILP or MIP)
* LA(Q), LA(Z) (NOT IMPLEMENTED YET)

Usage: toysolver [OPTION...] file.lp

    -h  --help           show help
    -v  --version        show version number
        --solver=SOLVER  mip (default), omega-test, cooper, old-mip

### toysat

SAT-based solver for the following problems:

* SAT
* PB
    * Pseudo Boolean Satisfaction (PBS)
    * Pseudo Boolean Optimization (PBO)
    * Weighted Boolean Optimization (WBO)
* Max-SAT
* Integer Programming (all variables must be bounded)

Usage:

    toysat [file.cnf||-]
    toysat --pb [file.opb|-]
    toysat --wbo [file.wbo|-]
    toysat --maxsat [file.cnf|file.wcnf|-]
    toysat --lp [file.lp|-]

### toyfmf

SAT-based finite model finder for first order logic (FOL).

Usage:

    toyfmf file.tptp size

### lp2yices

Converter from LP file to Yices input file.

Usage: lp2yice [file.lp|-]

    -h  --help      show help
        --optimize  output optimiality condition which uses quantifiers
        --no-check  do not output "(check)"

### cnf2lp

Converter from DIMACS .cnf file to .lp file.

Usage: cnf2lp [file.cnf|-]

### maxsat2lp

Converter from .cnf/.wcnf file to .lp file.

Usage: maxsat2lp [file.cnf|file.wcnf|-]

### pb2lp

Converter from .opb/.wbo file to .lp file.

Usage: pb2lp [--wbo] [file.opb|file.wbo|-]

TODO
----

* Cylindrical algebraic decomposition
* Local search
* Suvery propagation
