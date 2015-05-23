{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.PB2WBO
-- Copyright   :  (c) Masahiro Sakai 2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- References:
--
-- * Improving Unsatisfiability-based Algorithms for Boolean Optimization
--   <http://sat.inesc-id.pt/~ruben/talks/sat10-talk.pdf>
--
-----------------------------------------------------------------------------
module ToySolver.Converter.PB2WBO (convert) where

import qualified ToySolver.Data.PseudoBoolean as PBFile

convert :: PBFile.Formula -> PBFile.SoftFormula
convert formula
  = PBFile.SoftFormula
  { PBFile.wboTopCost = Nothing
  , PBFile.wboConstraints = cs1 ++ cs2
  , PBFile.wboNumVars = PBFile.pbNumVars formula
  , PBFile.wboNumConstraints = PBFile.pbNumConstraints formula + length cs2
  }
  where
    cs1 = [(Nothing, c) | c <- PBFile.pbConstraints formula]
    cs2 = case PBFile.pbObjectiveFunction formula of
            Nothing -> []
            Just e  ->
              [ if w >= 0
                then (Just w,       ([(-1,ls)], PBFile.Ge, 0))
                else (Just (abs w), ([(1,ls)],  PBFile.Ge, 1))
              | (w,ls) <- e
              ]
