# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

toysolver is a Haskell library and collection of command-line tools implementing solvers for SAT, SMT, Max-SAT, Pseudo-Boolean Optimization (PBO), Mixed Integer Linear Programming (MILP), and non-linear real arithmetic problems. It includes `toysat`, a moderately fast pure-Haskell SAT solver that placed 2nd in multiple categories at PB'12 competition.

## Build Commands

```bash
# Build (requires cloning with --recursive for SmtLib submodule)
stack build

# Build with parallel compilation
stack build --ghc-options=-j

# Build with optional components
stack build --flag toysolver:BuildToyFMF --flag toysolver:BuildSamplePrograms

# Run tests
stack test

# Run a specific test suite
stack test toysolver:test:TestSuite
stack test toysolver:test:TestPolynomial

# Run tests with a specific pattern (using tasty's --pattern)
stack test --test-arguments='--pattern "SAT"'

# Run benchmarks
stack bench

# Build documentation
stack haddock --no-haddock-deps

# Install executables locally
stack install
```

## Build Flags

Key cabal flags that can be enabled with `--flag toysolver:FlagName`:
- `BuildToyFMF` - Build finite model finder for first-order logic (requires logic-TPTP)
- `BuildSamplePrograms` - Build sample programs (sudoku, nonogram, nqueens, etc.)
- `BuildForeignLibraries` - Build toysat-ipasir C library (default: True)
- `WithZlib` - Enable gzip file support (default: True)
- `LinuxStatic` - Build statically linked binaries

## Architecture

### Core Library (`src/ToySolver/`)

**SAT Solving (`SAT/`)**
- `Solver/CDCL.hs` - Core CDCL SAT solver implementation
- `Encoder/` - Encoders for pseudo-boolean and cardinality constraints (Tseitin, Sequential Counter, Totalizer, etc.)
- `MUS/` - Minimally Unsatisfiable Subset enumeration algorithms
- `PBO/` - Pseudo-boolean optimization strategies
- `SLS/` - Stochastic local search (ProbSAT)

**Arithmetic (`Arith/`)**
- `Simplex.hs` - Simplex algorithm for linear arithmetic
- `Cooper.hs`, `OmegaTest.hs` - Integer linear arithmetic (quantifier elimination)
- `FourierMotzkin.hs` - Fourier-Motzkin elimination for real linear arithmetic
- `CAD.hs` - Cylindrical Algebraic Decomposition for non-linear real arithmetic
- `MIP.hs` - Mixed Integer Programming solver

**Data Structures (`Data/`)**
- `LA.hs` - Linear arithmetic expressions
- `Polynomial.hs` - Polynomial operations with factorization
- `AlgebraicNumber/` - Algebraic number arithmetic
- `FOL/` - First-order logic formulas

**Converters (`Converter/`)**
- Format converters between SAT, PB, MIP, QUBO, Max-SAT, and related problems
- Used by `toyconvert` command

**SMT (`SMT.hs`, `EUF/`)**
- SMT solver combining SAT with theory solvers
- Congruence closure for equality and uninterpreted functions

### Main Executables (`app/`)

- `toysolver.hs` - General arithmetic solver (MIP, SAT, PB, Max-SAT)
- `toysat/toysat.hs` - SAT-based solver (main solver, threaded)
- `toysmt/toysmt.hs` - SMT solver (QF_UF, QF_LRA, QF_RDL, QF_UFRDL, QF_UFLRA)
- `toyconvert.hs` - File format converter
- `toysolver_check.hs` - Solution checker
- `toyfmf.hs` - Finite model finder (optional, requires BuildToyFMF flag)
- `toysat-ipasir/` - C FFI library implementing IPASIR incremental SAT interface

### Test Organization (`test/`)

- `TestSuite.hs` - Main test suite with 33+ test modules
- `TestPolynomial.hs` - Polynomial-specific tests
- Test modules follow pattern `Test/*.hs` for each component

## Supported File Formats

| Format | Extension | Description |
|--------|-----------|-------------|
| DIMACS CNF | `.cnf` | SAT instances |
| WCNF | `.wcnf` | Weighted Max-SAT |
| OPB/WBO | `.opb`, `.wbo` | Pseudo-Boolean |
| LP/MPS | `.lp`, `.mps` | Linear/Mixed Integer Programming |
| SMT-LIB 2 | `.smt2` | SMT problems |
| QUBO | `.qubo` | Quadratic Unconstrained Binary Optimization |
| GCNF | `.gcnf` | Group-oriented CNF (for MUS) |

## GHC Compatibility

Tested with GHC 9.2 through 9.10. Default resolver in `stack.yaml` is lts-23.22 (GHC 9.8.4). Alternative stack configs are provided for other GHC versions (`stack-ghc-9.X.yaml`).

## Release Process

Documented in `doc/dev/release.md`. Key steps:
1. Run `misc/remove-trailing-space.rb` and other cleanup scripts
2. Update `CHANGELOG.markdown` and version in `toysolver.cabal`
3. Create git tag `v{VERSION}`
4. GitHub Actions creates release artifacts automatically
5. Upload to Hackage with `stack upload .`

## Related Packages

toysolver has spin-off packages maintained separately:
- `MIP`, `pseudo-boolean`, `data-interval`, `extended-reals`, `finite-field`, `OptDir`, `sign`, `bytestring-encoding`
- Backend drivers: `ersatz-toysat`, `satchmo-toysat`
