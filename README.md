toysolver
=========

[![License](https://img.shields.io/badge/License-BSD%203--Clause-blue.svg)](https://opensource.org/licenses/BSD-3-Clause)
[![Join the chat at https://gitter.im/msakai/toysolver](https://badges.gitter.im/Join%20Chat.svg)](https://gitter.im/msakai/toysolver)

Hackage:
[![Hackage](https://img.shields.io/hackage/v/toysolver.svg)](https://hackage.haskell.org/package/toysolver)
[![Hackage Deps](https://img.shields.io/hackage-deps/v/toysolver.svg)](https://packdeps.haskellers.com/feed?needle=toysolver)
[![Hackage CI](https://matrix.hackage.haskell.org/api/v2/packages/toysolver/badge)](https://matrix.hackage.haskell.org/#/package/toysolver)

Dev:
[![Build Status (Travis CI)](https://secure.travis-ci.org/msakai/toysolver.svg?branch=master)](http://travis-ci.org/msakai/toysolver)
[![Build Status (AppVeyor)](https://ci.appveyor.com/api/projects/status/w7g615sp8ysiqk7w/branch/master?svg=true)](https://ci.appveyor.com/project/msakai/toysolver/branch/master)
[![Build Status (GitHub Actions)](https://github.com/msakai/toysolver/workflows/build/badge.svg)](https://github.com/msakai/toysolver/actions)
[![Coverage Status](https://coveralls.io/repos/msakai/toysolver/badge.svg)](https://coveralls.io/r/msakai/toysolver)

It provides solver implementations of various problems including SAT, SMT, Max-SAT, PBS (Pseudo Boolean Satisfaction), PBO (Pseudo Boolean Optimization), MILP (Mixed Integer Linear Programming) and non-linear real arithmetic.

In particular it contains moderately-fast pure-Haskell SAT solver 'toysat'.

Installation
------------

### Installation from binaries

Binary distributions for Windows, Mac, and Linux, can be downloaded from [releases](https://github.com/msakai/toysolver/releases) page.

### Installation from Hackage

`cabal install toysolver` or `stack install toysolver`

### Installation from source using `stack`

1. [Install `stack`](https://docs.haskellstack.org/en/stable/README/#how-to-install)
2. `git clone --recursive https://github.com/msakai/toysolver.git`
3. `cd toysolver`
4. `stack install`

### Installation from source using `cabal-install`

1. Install [GHC](https://www.haskell.org/ghc/) and [cabal](https://www.haskell.org/cabal/#install-upgrade) (You can use [ghcup](https://gitlab.haskell.org/haskell/ghcup-hs#installation) for installing them)
2. `git clone --recursive https://github.com/msakai/toysolver.git`
3. `cd toysolver`
4. `cabal install`

### Docker image

The Docker images can be found at [dockerhub](https://hub.docker.com/repository/docker/msakai/toysolver).

To run `toysat` using Docker for solving `samples/pbs/normalized-j3025_1-sat.opb`:

```
docker run -it --rm -v `pwd`:/data msakai/toysolver toysat samples/pbs/normalized-j3025_1-sat.opb`
```

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
