{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Converter.WBO2PB
-- Copyright   :  (c) Masahiro Sakai 2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module Converter.WBO2PB (convert) where

import Data.Array.IArray
import qualified SAT.Types as SAT
import qualified Text.PBFile as PBFile

convert :: PBFile.SoftFormula -> (PBFile.Formula, SAT.Model -> SAT.Model)
convert wbo@(top, cs) = ((Just obj, topConstr ++ concatMap f cm), mtrans)
  where
    nv = PBFile.wboNumVars wbo

    cm  = zip [nv+1..] cs
    obj = [(w, [i]) | (i, (Just w,_)) <- cm]

    f :: (PBFile.Var, PBFile.SoftConstraint) -> [PBFile.Constraint]
    f (_, (Nothing, c)) = return c
    f (i, (Just _, c))  = relax i c

    relax :: PBFile.Var -> PBFile.Constraint -> [PBFile.Constraint]
    relax i (lhs, PBFile.Ge, rhs) = [((d, [i]) : lhs, PBFile.Ge, rhs)]
      where
        d = rhs - SAT.pbLowerBound [(c,1) | (c,_) <- lhs]
    relax i (lhs, PBFile.Eq, rhs) =
      relax i (lhs, PBFile.Ge, rhs) ++
      relax i ([(-c,ls) | (c,ls) <- lhs], PBFile.Ge, - rhs)

    topConstr :: [PBFile.Constraint]
    topConstr = 
     case top of
       Nothing -> []
       Just t -> [([(-c,ls) | (c,ls) <- obj], PBFile.Ge, - (t - 1))]

    mtrans :: SAT.Model -> SAT.Model
    mtrans m = 
      array (1, nv) [(x, m ! x) | x <- [1..nv]]
