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

