{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Converter.PB2WBO
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
module Converter.PB2WBO (convert) where

import qualified Text.PBFile as PBFile

convert :: PBFile.Formula -> PBFile.SoftFormula
convert (obj, cs) = (Nothing, cs1 ++ cs2)
  where
    cs1 = [(Nothing, c) | c <- cs]
    cs2 = case obj of
            Nothing -> []
            Just e  ->
              [ if w >= 0
                then (Just w,       ([(-1,ls)], PBFile.Ge, 0))
                else (Just (abs w), ([(1,ls)],  PBFile.Ge, 1))
              | (w,ls) <- e
              ]
