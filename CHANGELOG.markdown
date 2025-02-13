0.9.0 (Unreleased)
-----

* Converters updates
  * Add `--dump-info` option to `toyconvert` (#119, #120, #125)
  * Change the signs of QUBO-related converter's representation of offset (#126)
  * Change `WBO2IPInfo` not to store weights (#124)
  * Change `SAT2KSATInfo`, `SimplifyMaxSAT2Info` and `SAT3ToMaxSAT2Info` to be synonyms of `TseitinInfo` (#121, #123)
  * Use `SAT.VarMap` to represent definitions in SAT-related encoders/converters (#127)
  * Add instances for transforming objective function values between PB↔WBO conversion (#132)
  * Change `ReversedTransformer`, `GCNF2MaxSATInfo`, `PBAsQUBOInfo`, `QUBO2IsingInfo`, `Ising2QUBOInfo` from `data` to `newtype` (#134)
  * Fix `mip2pb`’s handling of indicator constraints (#137)
  * Add more converter instances (#138)
  * Restructure converter modules (#142)
  * Support SOS constraints over non-binary variables in `mip2pb` (#140)
  * Rename `mip2pb` to `ip2pb`
* Pseudo-boolean and cardinality constarint encoder updates
  * Consider polarity in encoding of pseudo-boolean and cardinality constraints (#88)
  * Add BC-CNF pseudo boolean constraint encoder (#85)
  * Support specifying PB encoding strategy (#77)
* Dependencies
  * Support GHC 9.4 (#92), 9.6, 9.8, 9.10
  * Use `prettyprinter` package if `optparse-applicative` is `>=0.18` (#106)
  * Upgrade `MIP` package to 0.2.* (#144)
* Misc
  * Do not rely on `StarIsType` extension (#84)
  * Add `BuildForeignLibraries` flag (#94)
  * Remove features that depend on OpenCL (#90)
  * Improve `ToySolver.Graph` module (#130, #150)

0.8.0
-----

* Separate Formula type from `ToySolver.SAT.Encoder.Tseitin` into `ToySolver.SAT.Formula` (#74)
* Use `megaparsec` as default PB parser and add `--pb-fast-parser` option to use `attoparsec` (#71)
* Update lower bounds of dependency packages
* Add `--maxsat-compact-v-line` option for printing MaxSAT solution in the new compact format (#65)
* Fix `ToySolver.SAT`.Printer and its toysat's output for Max-SAT problems  (#64)
* Support new WCNF file format (#63)
* Use bytestring-encoding-0.1.1.0 because bytestring-encoding-0.1.0.0 has a memory corruption bug (#62)
* Remove deprecated API (#56)
* Support GHC-9.2 (#76) and stop supporting GHC 8.0, 8.2, and 8.4 (#50)

0.7.0
-----

* add `toysat-ipasir` foreign library which implements [IPASIR](https://github.com/biotomas/ipasir) API for incremental SAT solving.
* `ToySolver.SAT`
  * Restructure SAT solver modules under `ToySolver.SAT.Solver.*`
  * add `SequentialCounter`, `ParallelCounter` and `Totalizer` as methods for encoding cardinality constraints
  * add `PackedLit` type to reduce memory footprint
  * use structure of array (SOA) approach to reduce memory footprint
  * add `setLearnCallback`/`clearLearnCallback` and `setTerminateCallback`/`clearTerminateCallback` which correspond to [IPASIR](https://github.com/biotomas/ipasir)'s `ipasir_set_learn()` and `ipasir_set_terminate()`.
  * add `clearLogger`
  * change `getFailedAssumptions` and `getAssumptionsImplications` to return `IntSet` instead of `[Int]`
* separate `ToySolver.Data.MIP.*` into new [MIP](http://hackage.haskell.org/package/MIP) package's `Numeric.Optimization.MIP.*`
* add `ToySolver.Data.Polynomial.Interpolation.Hermite`
* add `ToySolver.Graph.Base` and `ToySolver.Graph.MaxCut`
* add `ToySolver.Converter.SAT2MIS`
* `ToySolver.Graph.ShortestPath`: fix vertex type to `Int` instead of arbitrary `Hashable` type
* stop supporting GHC-7.10
* add `ExtraBoundsChecking` flag for debugging

0.6.0
-----
* new solvers:
  * `ToySolver.SAT.SLS.ProbSAT` and sample `probsat` program
* new converters:
  * `ToySolver.Converter.NAESAT`
  * `ToySolver.Converter.SAT2MaxCut`
  * `ToySolver.Converter.SAT2MaxSAT`: SAT and 3-SAT to Max-2-SAT converter
  * `ToySolver.Converter.QBF2IPC`
  * `ToySolver.Converter.QUBO`: QUBO↔IsingModel converter
* new file format API:
  * merge `ToySolver.Text.MaxSAT`, `ToySolver.Text.GCNF`, `ToySolver.Text.QDimacs`, and `ToySolver.Text.CNF`
    info `ToySolver.FileFormat` and `ToySolver.FileFormat.CNF`
  * allow reading/writing `gzip`ped CNF/WCNF/GCNF/QDimacs/LP/MPS files
* rename modules:
  * `ToySolver.Arith.Simplex2` to `ToySolver.Arith.Simplex`
  * `ToySolver.Arith.MIPSolver2` to `ToySolver.Arith.MIP`
  * `ToySolver.Data.Var` to `ToySolver.Data.IntVar`
* `ToySolver.SAT`:
  * add `cancel` function for interruption
  * introduce `PackedClause` type
* `ToySolver.Arith.Simplex`
  * introduce `Config` data type
  * implement bound tightening
* switch from `System.Console.GetOpt` to `optparse-applicative`
* stop supporting GHC-7.8

0.5.0
-----
* new solvers:
  * `ToySolver.BitVector`
  * `ToySolver.Combinatorial.BipartiteMatching`
  * `ToySolver.Combinatorial.HittingSet.DAA`
  * `ToySolver.Combinatorial.HittingSet.MARCO`
  * `ToySolver.Arith.DifferenceLogic`
  * `ToySolver.Graph.ShortestPath`
  * `ToySolver.QBF`
* `toysat`
  * add `--init-sp` option to initialize variable state using survey propagation
  * allow using `UBCSAT` when solving PBO/WBO problems
* `toysmt`
  * suport bit-vector logic
* `toyconvert`
  * `pbconvert` and `lpconvert` were merged into a single command `toyconvert`
  * add `--ksat=NUMBER` option to convert to k-SAT formula
  * add `--linearlize` and `--linearizer-pb` options
  * add `--remove-usercuts` option
* add new modules to `ToySolver.Converter`
  * `ToySolver.Converter.GCNF2MaxSAT`
  * `ToySolver.Converter.MIP2PB`
  * `ToySolver.Converter.PBLinearlization`
  * `ToySolver.Converter.SAT2KSAT`
* `ToySolver.SAT`
  * introduce type classes for adding constraints
  * `ToySolver.SAT.Encoder.Tseitin`: add XOR and Full-adder encoder
  * `ToySolver.SAT.Encoder.PB`: add functionality to encode PB constraint using adder networks and sorting networks
  * `ToySolver.SAT.MUS.Enum`: add `GurvichKhachiyan1999` and `MARCO` to the MUS enumeration methods
  * implement learning rate based branching heuristics
  * add `ToySolver.SAT.ExistentialQuantification`
  * add `ToySolver.SAT.Store.CNF` and `ToySolver.SAT.Store.PB`
  * implement survey propagation as `ToySolver.SAT.MessagePassing.SurveyPropagation`
* `Data.MIP`
  * parameterize Problem type with coefficient type and use `Scientific` as default
  * introduce `Status` type
  * add solution file parsers: `ToySolver.Data.MIP.Solution.{CBC,CPLEX,GLPK,Gurobi,SCIP}`
  * add solver wrapper modules: `ToySolver.MIP.Solver.{CBC,CPLEX,Glpsol,GurobiCl,LPSolve,SCIP}`
* add a QDimacs parser as `ToySolver.Text.QDimacs`
* add `ToySolver.Text.CNF`, `ToySolver.Text.QDimacs`
* switch to use `megaparsec`
* use `clock` package for measuring duration
* add simple numberlink solver sample

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

