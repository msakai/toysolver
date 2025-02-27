toysolver
=========

[![License](https://img.shields.io/badge/License-BSD%203--Clause-blue.svg)](https://opensource.org/licenses/BSD-3-Clause)
[![Join the chat at https://gitter.im/msakai/toysolver](https://badges.gitter.im/Join%20Chat.svg)](https://gitter.im/msakai/toysolver)

Hackage:
[![Hackage](https://img.shields.io/hackage/v/toysolver.svg)](https://hackage.haskell.org/package/toysolver)

Dev:
[![Build Status](https://github.com/msakai/toysolver/workflows/build/badge.svg)](https://github.com/msakai/toysolver/actions)
[![Coverage Status](https://coveralls.io/repos/msakai/toysolver/badge.svg)](https://coveralls.io/r/msakai/toysolver)

It provides solver implementations of various problems including SAT, SMT, Max-SAT, PBS (Pseudo Boolean Satisfaction), PBO (Pseudo Boolean Optimization), MILP (Mixed Integer Linear Programming) and non-linear real arithmetic.

In particular, it contains moderately-fast pure-Haskell SAT solver 'toysat'.

Installation
------------

See [INSTALL.md](INSTALL.md).

Usage
-----

This package includes several commands.

### toysolver

Arithmetic solver for the following problems:

* Mixed Integer Linear Programming (MILP or MIP)
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

### toysmt

SMT solver based on toysat.

Usage:

    toysmt [file.smt2]

Currently only QF_UF, QF_RDL, QF_LRA, QF_UFRDL and QF_UFLRA logic are supported.

### toyfmf

SAT-based finite model finder for first order logic (FOL).

Usage:

    toyfmf [file.tptp] [size]

### toyconvert

Converter between various problem files.

Usage:

    toyconvert -o [outputfile] [inputfile]

Supported formats:

* Input formats: .cnf .wcnf .opb .wbo .gcnf .lp .mps
* Output formats: .cnf .wcnf .opb .wbo .lsp .lp .mps .smp .smt2 .ys

Bindings
--------

* [ersatz-toysat](http://hackage.haskell.org/package/ersatz-toysat) -  toysat backend driver for [ersatz](http://hackage.haskell.org/package/ersatz)
* [satchmo-toysat](http://hackage.haskell.org/package/satchmo-toysat) - toysat backend driver for [satchmo](http://hackage.haskell.org/package/satchmo)

Spin-off projects and packages
------------------------------

* [bytestring-encoding](https://github.com/msakai/bytestring-encoding)
* [data-interval](https://github.com/msakai/data-interval)	
* [extended-reals](https://github.com/msakai/extended-reals)
* [finite-field](https://github.com/msakai/finite-field)
* [MIP](https://github.com/msakai/haskell-MIP)
* [OptDir](https://github.com/msakai/haskell-optdir)
* [pseudo-boolean](https://github.com/msakai/pseudo-boolean)
* [sign](https://github.com/msakai/sign)
