{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Converter.MaxSAT2LP
-- Copyright   :  (c) Masahiro Sakai 2011-2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-----------------------------------------------------------------------------
module Converter.MaxSAT2LP
  ( convert
  ) where

import Data.Array.IArray
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Text.LPFile as LPFile
import qualified Text.MaxSAT as MaxSAT
import SAT.Types

convert :: MaxSAT.WCNF -> (LPFile.LP, Map.Map LPFile.Var Rational -> Model)
convert (nvar, top, ls) = (lp, mtrans)
  where
    lp = LPFile.LP
      { LPFile.variables = Set.fromList vs
      , LPFile.dir = LPFile.OptMin
      , LPFile.objectiveFunction = (Nothing, obj)
      , LPFile.constraints = cs
      , LPFile.bounds = Map.empty
      , LPFile.integerVariables = Set.empty
      , LPFile.binaryVariables = Set.fromList vs
      , LPFile.semiContinuousVariables = Set.empty
      , LPFile.sos = []
      }
    mtrans m =
      array (1, nvar)
        [　(i, val)
        | i <- [1 .. nvar]
        , let val =
                case m Map.! ("x" ++ show i) of
                  0  -> False
                  1  -> True
                  v0 -> error (show v0 ++ " is neither 0 nor 1")
        ]

    obj = [ LPFile.Term (fromIntegral w) [v] | (v,(w,_)) <- zs, w < top ]
    vs = [ "x" ++ show n | n <- [(1::Int)..nvar]] ++ 
         [ z | (z,(w,_)) <- zs, w /= top ]
    cs = [h (z,(w,xs)) | (z,(w,xs)) <- zs]
      where
        h (z,(w,xs)) = LPFile.Constraint
          { LPFile.constrType      = LPFile.NormalConstraint
          , LPFile.constrLabel     = Nothing
          , LPFile.constrIndicator = Nothing
          , LPFile.constrBody      = 
              case f xs of
                (s,n)
                  | w>=top    -> (g s, LPFile.Ge, fromIntegral (1 - n)) -- hard constraint
                  | otherwise -> (LPFile.Term 1 [z] : g s, LPFile.Ge, fromIntegral (1 - n)) -- soft constraint
          }

    zs = zip (map (\x -> "z" ++ show x) [(1::Int)..]) ls

    f :: [Lit] -> (Map.Map Var Int, Int)
    f = foldr phi (Map.empty,0)
      where        
        phi lit (s,m)
         | lit >= 0  = (Map.insertWith (+) (abs lit) 1 s, m)
         | otherwise = (Map.insertWith (+) (abs lit) (-1) s, m+1)

    g :: Map.Map Var Int -> [LPFile.Term]
    g m = do
      (v,c) <- Map.toList m
      return (LPFile.Term (fromIntegral c) ["x" ++ show v])
