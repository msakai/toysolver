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
  ( MUS
  , MCS
  , MSS
  ) where

import ToySolver.SAT.Types

-- | Minimal Unsatisfiable Subset of constraints (MUS).
--
-- A subset U ⊆ C is an MUS if U is unsatisfiable and ∀C_i ∈ U, U\\{C_i} is satisfiable [CAMUS]. 
type MUS = [Lit]

-- | Minimal Correction Subset of constraints (MCS).
--
-- A subset M ⊆ C is an MCS if C\\M is satisfiable and ∀C_i ∈ M, C\\(M\\{C_i}) is unsatisfiable [CAMUS].
-- A MCS is the complement of an MSS and also known as a CoMSS.
type MCS = [Lit]

-- | Maximal Satisfiable Subset (MSS).
--
-- A subset S ⊆ C is an MSS if S is satisfiable and ∀C_i ∈ U\\S, S∪{C_i} is unsatisfiable [CAMUS].
type MSS = [Lit]
