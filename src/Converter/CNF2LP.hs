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
import qualified SAT.Types as SAT
import Converter.ObjType

convert :: ObjType -> DIMACS.CNF -> (LPFile.LP, Map.Map LPFile.Var Rational -> SAT.Model)
convert objType cnf = (lp, mtrans)
  where
    lp = LPFile.LP
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
    mtrans m =
      array (1, DIMACS.numVars cnf)
        [　(i, val)
        | i <- [1 .. DIMACS.numVars cnf]
        , let val =
                case m Map.! ("x" ++ show i) of
                  0 -> False
                  1 -> True
                  v0 -> error (show v0 ++ " is neither 0 nor 1")
        ]
  
    dir = if objType == ObjMaxZero then OptMin else OptMax
    obj = if objType == ObjNone then [LPFile.Term 0 (take 1 vs)] else [LPFile.Term 1 [v] | v <- vs]
    vs = if DIMACS.numVars cnf == 0
         then ["x0"]
         else ["x" ++ show i | i <- [1 .. DIMACS.numVars cnf]]
    cs = do
      cl <- DIMACS.clauses cnf      
      let (lhs,n) = foldr f ([], 0) (elems cl)
      return $ LPFile.Constraint
        { LPFile.constrType      = LPFile.NormalConstraint
        , LPFile.constrLabel     = Nothing
        , LPFile.constrIndicator = Nothing
        , LPFile.constrBody      = (lhs, LPFile.Ge, fromIntegral $ 1 - n)
        }
    f :: Int -> (LPFile.Expr,Integer) -> (LPFile.Expr,Integer)
    f lit (es,n) =
      if lit > 0
      then (LPFile.Term 1 [v] : es, n)
      else (LPFile.Term (-1) [v] : es, n+1)
      where v = "x" ++ show (abs lit)
