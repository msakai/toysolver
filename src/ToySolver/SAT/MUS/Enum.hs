-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.MUS.Enum
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
-- * [HYCAM] A. Gregoire, B. Mazure, and C. Piette, Boosting a complete
--   technique to find MSS and MUS: thanks to a local search oracle, in
--   Proceedings of the 20th international joint conference on Artifical
--   intelligence, ser. IJCAI'07. San Francisco, CA, USA: Morgan Kaufmann
--   Publishers Inc., 2007, pp. 2300-2305.
--   <http://ijcai.org/papers07/Papers/IJCAI07-370.pdf>
--
-- * [DAA] J. Bailey and P. Stuckey, Discovery of minimal unsatisfiable
--   subsets of constraints using hitting set dualization," in Practical
--   Aspects of Declarative Languages, pp. 174-186, 2005.
--   <http://ww2.cs.mu.oz.au/~pjs/papers/padl05.pdf>
--
-----------------------------------------------------------------------------
module ToySolver.SAT.MUS.Enum
  ( module ToySolver.SAT.MUS.Types
  , Method (..)
  , showMethod
  , parseMethod
  , Options (..)
  , allMUSAssumptions
  ) where

import Data.Char
import qualified ToySolver.SAT as SAT
import ToySolver.SAT.Types
import ToySolver.SAT.MUS.Types
import ToySolver.SAT.MUS.Enum.Base
import qualified ToySolver.SAT.MUS.Enum.CAMUS as CAMUS
import qualified ToySolver.SAT.MUS.Enum.DAA as DAA

showMethod :: Method -> String
showMethod m = map toLower (show m)

parseMethod :: String -> Maybe Method
parseMethod s =
  case map toLower s of
    "camus" -> Just CAMUS
    "daa" -> Just DAA
    _ -> Nothing

allMUSAssumptions :: SAT.Solver -> [Lit] -> Options -> IO ([MUS], [MCS])
allMUSAssumptions solver sels opt =
  case optMethod opt of
    CAMUS -> CAMUS.allMUSAssumptions solver sels opt
    DAA -> DAA.allMUSAssumptions solver sels opt
