{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.SAT.MUS
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Minimal Unsatifiable Subset (MUS) Finder
--
-- References:
--
-- * Ulrich Junker. QuickXplain: Preferred explanations and relaxations for
--   over-constrained problems. In Proc. of AAAI’04, pages 167-172, 2004.
--   <http://www.aaai.org/Papers/AAAI/2004/AAAI04-027.pdf>
--
-----------------------------------------------------------------------------
module ToySolver.SAT.MUS
  ( module ToySolver.SAT.MUS.Types
  , Method (..)
  , showMethod
  , parseMethod
  , Options (..)
  , findMUSAssumptions
  ) where

import Data.Char
import qualified ToySolver.SAT as SAT
import ToySolver.SAT.MUS.Base
import ToySolver.SAT.MUS.Types
import qualified ToySolver.SAT.MUS.Deletion as Deletion
import qualified ToySolver.SAT.MUS.Insertion as Insertion
import qualified ToySolver.SAT.MUS.QuickXplain as QuickXplain

showMethod :: Method -> String
showMethod m = map toLower (show m)

parseMethod :: String -> Maybe Method
parseMethod s =
  case map toLower s of
    "linear" -> Just Deletion
    "deletion" -> Just Deletion
    "insertion" -> Just Insertion
    "quickxplain" -> Just QuickXplain
    _ -> Nothing

-- | Find a minimal set of assumptions that causes a conflict.
-- Initial set of assumptions is taken from 'SAT.getFailedAssumptions'.
findMUSAssumptions
  :: SAT.Solver
  -> Options
  -> IO MUS
findMUSAssumptions solver opt =
  case optMethod opt of
    Deletion -> Deletion.findMUSAssumptions solver opt
    Insertion -> Insertion.findMUSAssumptions solver opt
    QuickXplain -> QuickXplain.findMUSAssumptions solver opt
