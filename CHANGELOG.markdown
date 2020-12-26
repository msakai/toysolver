0.7.0 (Unreleased)
-----
* `ToySolver.Data.MIP.*` is separated into `MIP` package as `Numeric.Optimization.MIP`

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
  *	`ToySolver.Arith.Simplex2` to `ToySolver.Arith.Simplex`
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

