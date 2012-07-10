{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Converter.CNF2LP
-- Copyright   :  (c) Masahiro Sakai 2011-2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module Converter.CNF2LP
  ( ObjType (..)
  , convert 
  ) where

import Data.Array.IArray
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.OptDir
import qualified Text.LPFile as LPFile
import qualified Language.CNF.Parse.ParseDIMACS as DIMACS
import Converter.ObjType

convert :: DIMACS.CNF -> ObjType -> LPFile.LP
convert cnf objType
  = LPFile.LP
  { LPFile.variables = Set.fromList vs
  , LPFile.dir = dir
  , LPFile.objectiveFunction = (Nothing, obj)
  , LPFile.constraints = cs
  , LPFile.bounds = Map.empty
  , LPFile.integerVariables = Set.empty
  , LPFile.binaryVariables = Set.fromList vs
  , LPFile.semiContinuousVariables = Set.empty
  , LPFile.sos = []
  }
  where
    dir = if objType == ObjMaxZero then OptMin else OptMax
    obj = if objType == ObjNone then [LPFile.Term 0 (take 1 vs)] else [LPFile.Term 1 [v] | v <- vs]
    vs = if DIMACS.numVars cnf == 0
         then ["x0"]
         else ["x" ++ show i | i <- [1 .. DIMACS.numVars cnf]]
    cs = do
      cl <- DIMACS.clauses cnf      
      let (lhs,n) = foldr f ([], 0) (elems cl)
      return (Nothing, Nothing, (lhs, LPFile.Ge, fromIntegral $ 1 - n))
    f :: Int -> (LPFile.Expr,Integer) -> (LPFile.Expr,Integer)
    f lit (es,n) =
      if lit > 0
      then (LPFile.Term 1 [v] : es, n)
      else (LPFile.Term (-1) [v] : es, n+1)
      where v = "x" ++ show (abs lit)
