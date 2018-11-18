{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE TypeFamilies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.QUBO
-- Copyright   :  (c) Masahiro Sakai 2018
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
-- 
-----------------------------------------------------------------------------
module ToySolver.Converter.QUBO
  ( qubo2pbo
  , QUBO2PBOInfo (..)

  , pboAsQUBO
  , PBOAsQUBOInfo
  ) where

import Control.Monad
import Control.Monad.State
import Data.Array.Unboxed
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.Maybe
import qualified Data.PseudoBoolean as PBFile
import ToySolver.Converter.Base
import qualified ToySolver.QUBO as QUBO
import qualified ToySolver.SAT.Types as SAT

-- -----------------------------------------------------------------------------

qubo2pbo :: QUBO.Problem Integer -> (PBFile.Formula, QUBO2PBOInfo)
qubo2pbo prob =
  ( PBFile.Formula
    { PBFile.pbObjectiveFunction = Just $
        [ (c, if x1==x2 then [x1+1] else [x1+1, x2+1])
        | (x1, row) <- IntMap.toList $ QUBO.quboMatrix prob
        , (x2, c) <- IntMap.toList row
        ]
    , PBFile.pbConstraints = []
    , PBFile.pbNumVars = QUBO.quboNumVars prob
    , PBFile.pbNumConstraints = 0
    }
  , QUBO2PBOInfo
  )

data QUBO2PBOInfo = QUBO2PBOInfo

instance Transformer QUBO2PBOInfo where
  type Source QUBO2PBOInfo = QUBO.Solution
  type Target QUBO2PBOInfo = SAT.Model

instance ForwardTransformer QUBO2PBOInfo where
  transformForward QUBO2PBOInfo sol = ixmap (lb+1,ub+1) (subtract 1) sol
    where
      (lb,ub) = bounds sol

instance BackwardTransformer QUBO2PBOInfo where
  transformBackward QUBO2PBOInfo m = ixmap (lb-1,ub-1) (+1) m
    where
      (lb,ub) = bounds m

-- -----------------------------------------------------------------------------

pboAsQUBO :: PBFile.Formula -> Maybe (QUBO.Problem Integer, PBOAsQUBOInfo)
pboAsQUBO formula = do
  (prob, offset) <- runStateT body 0
  return $ (prob, PBOAsQUBOInfo offset)
  where

    body :: StateT Integer Maybe (QUBO.Problem Integer)
    body = do
      guard $ null (PBFile.pbConstraints formula)
      let f :: PBFile.WeightedTerm -> StateT Integer Maybe [(Integer, Int, Int)]
          f (c,[]) = modify (+c) >> return []
          f (c,[x]) = return [(c,x,x)]
          f (c,[x1,x2]) = return [(c,x1,x2)]
          f _ = mzero
      xs <- mapM f $ SAT.removeNegationFromPBSum $ fromMaybe [] $ PBFile.pbObjectiveFunction formula
      return $
        QUBO.Problem
        { QUBO.quboNumVars = PBFile.pbNumVars formula
        , QUBO.quboMatrix = mkMat $
            [ (x1', x2', c)
            | (c,x1,x2) <- concat xs, let x1' = min x1 x2 - 1, let x2' = max x1 x2 - 1
            ]
        }

data PBOAsQUBOInfo = PBOAsQUBOInfo !Integer

instance Transformer PBOAsQUBOInfo where
  type Source PBOAsQUBOInfo = SAT.Model
  type Target PBOAsQUBOInfo = QUBO.Solution

instance ForwardTransformer PBOAsQUBOInfo where
  transformForward (PBOAsQUBOInfo _offset) m = ixmap (lb-1,ub-1) (+1) m
    where
      (lb,ub) = bounds m

instance BackwardTransformer PBOAsQUBOInfo where
  transformBackward (PBOAsQUBOInfo _offset) sol = ixmap (lb+1,ub+1) (subtract 1) sol
    where
      (lb,ub) = bounds sol

-- -----------------------------------------------------------------------------

mkMat :: (Eq a, Num a) => [(Int,Int,a)] -> IntMap (IntMap a)
mkMat m = normalizeMat $
  IntMap.unionsWith (IntMap.unionWith (+)) $
  [IntMap.singleton i (IntMap.singleton j qij) | (i,j,qij) <- m]

normalizeMat :: (Eq a, Num a) => IntMap (IntMap a) -> IntMap (IntMap a)
normalizeMat = IntMap.mapMaybe ((\m -> if IntMap.null m then Nothing else Just m) . normalizeVec)

normalizeVec :: (Eq a, Num a) => IntMap a -> IntMap a
normalizeVec = IntMap.filter (/=0)
