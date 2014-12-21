toysolver
=========

[![Build Status](https://secure.travis-ci.org/msakai/toysolver.png?branch=master)](http://travis-ci.org/msakai/toysolver) [![Hackage](https://budueba.com/hackage/toysolver)](https://hackage.haskell.org/package/toysolver)

Assorted decision procedures for SAT, Max-SAT, PB, MIP, etc.

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
* Boolean SATisfiability problem (SAT)
* PB
    * Pseudo Boolean Satisfaction (PBS)
    * Pseudo Boolean Optimization (PBO)
    * Weighted Boolean Optimization (WBO)
* Max-SAT families
    * Max-SAT
    * Partial Max-SAT
    * Weighted Max-SAT
    * Weighted Partial Max-SAT
* Real Closed Field
* LA(Q), LA(Z) (NOT IMPLEMENTED YET)

Usage:

    toysolver [OPTION...] [file.lp|file.mps]
    toysolver --lp [OPTION...] [file.lp|file.mps]
    toysolver --sat [OPTION...] [file.cnf]
    toysolver --pb [OPTION...] [file.opb]
    toysolver --wbo [OPTION...] [file.wbo]
    toysolver --maxsat [OPTION...] [file.cnf|file.wcnf]

    -h  --help           show help
    -v  --version        show version number
        --solver=SOLVER  mip (default), omega-test, cooper, cad, old-mip, ct

### toysat

SAT-based solver for the following problems:

* SAT
    * Boolean SATisfiability problem (SAT)
    * Minimally Unsatisfiable Subset (MUS)
    * Group-Oriented MUS (GMUS)
* PB
    * Pseudo Boolean Satisfaction (PBS)
    * Pseudo Boolean Optimization (PBO)
    * Weighted Boolean Optimization (WBO)
* Max-SAT families
    * Max-SAT
    * Partial Max-SAT
    * Weighted Max-SAT
    * Weighted Partial Max-SAT
* Integer Programming (all variables must be bounded)

Usage:

    toysat [file.cnf|-]
    toysat --sat [file.cnf|-]
    toysat --mus [file.gcnf|file.cnf|-]
    toysat --pb [file.opb|-]
    toysat --wbo [file.wbo|-]
    toysat --maxsat [file.cnf|file.wcnf|-]
    toysat --lp [file.lp|file.mps|-]

PB'12 competition result: 

* toysat placed 2nd in PARTIAL-BIGINT-LIN and SOFT-BIGINT-LIN categories
* toysat placed 4th in PARTIAL-SMALLINT-LIN and SOFT-SMALLINT-LIN categories
* toysat placed 8th in OPT-BIGINT-LIN category

### toyfmf

SAT-based finite model finder for first order logic (FOL).

Usage:

    toyfmf [file.tptp] [size]

### lpconvert

Converter between LP/MIP/SAT-related formats

Usage:

    lpconvert -o [outputfile] [inputfile]

Supported formats:

* Input formats: lp, mps, cnf, wcnf, opb, wbo
* Output formats: lp, .mps, smt2, ys

### pbconvert

Converter between SAT/PB-related formats

Usage:

    pbconvert -o [outputfile] [inputfile]

Supported formats:

* Input formats: cnf, wcnf, opb, wbo
* Output formats: opb, wbo, lsp, lp, mps, smp, smt2, ys

TODO
----

* Local search
* Suvery propagation
