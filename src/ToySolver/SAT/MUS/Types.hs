-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.MUS.Types
-- Copyright   :  (c) Masahiro Sakai 2012-2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- In this module, we assume each soft constraint /C_i/ is represented as a literal.
-- If a constraint /C_i/ is not a literal, we can represent it as a fresh variable /v/
-- together with a hard constraint /v ⇒ C_i/.
--
-- References:
--
-- * [CAMUS] M. Liffiton and K. Sakallah, Algorithms for computing minimal
--   unsatisfiable subsets of constraints, Journal of Automated Reasoning,
--   vol. 40, no. 1, pp. 1-33, Jan. 2008. 
--   <http://sun.iwu.edu/~mliffito/publications/jar_liffiton_CAMUS.pdf>
--
-----------------------------------------------------------------------------
module ToySolver.SAT.MUS.Types
  ( US
  , MUS
  , CS
  , MCS
  , SS
  , MSS
  ) where

import ToySolver.SAT.Types

-- | Unsatisfiable Subset of constraints (US).
--
-- A subset U ⊆ C is an US if U is unsatisfiable. 
type US = LitSet

-- | Minimal Unsatisfiable Subset of constraints (MUS).
--
-- A subset U ⊆ C is an MUS if U is unsatisfiable and ∀C_i ∈ U, U\\{C_i} is satisfiable [CAMUS]. 
type MUS = LitSet

-- | Correction Subset of constraints (CS).
--
-- A subset M ⊆ C is a CS if C\\M is satisfiable.
-- A CS is the complement of a 'SS'.
type CS = LitSet

-- | Minimal Correction Subset of constraints (MCS).
--
-- A subset M ⊆ C is an MCS if C\\M is satisfiable and ∀C_i ∈ M, C\\(M\\{C_i}) is unsatisfiable [CAMUS].
-- A MCS is the complement of an 'MSS' and also known as a CoMSS.
type MCS = LitSet

-- | Satisfiable Subset (SS).
--
-- A subset S ⊆ C is a SS if S is satisfiable.
-- A SS is the complement of a 'CS'.
type SS = LitSet

-- | Maximal Satisfiable Subset (MSS).
--
-- A subset S ⊆ C is an MSS if S is satisfiable and ∀C_i ∈ U\\S, S∪{C_i} is unsatisfiable [CAMUS].
-- A MSS is the complement of an 'MCS'.
type MSS = LitSet
