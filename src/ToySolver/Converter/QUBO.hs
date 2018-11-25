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
  , PBOAsQUBOInfo (..)

  , qubo2ising
  , QUBO2IsingInfo (..)

  , ising2qubo
  , Ising2QUBOInfo (..)
  ) where

import Control.Monad
import Control.Monad.State
import Data.Array.Unboxed
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.List
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
  deriving (Eq, Show)

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
  deriving (Eq, Show)

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

qubo2ising :: (Eq a, Show a, Num a) => QUBO.Problem a -> (QUBO.IsingModel a, QUBO2IsingInfo a)
qubo2ising QUBO.Problem{ QUBO.quboNumVars = n, QUBO.quboMatrix = qq } =
  ( QUBO.IsingModel
    { QUBO.isingNumVars = n
    , QUBO.isingInteraction = normalizeMat $ jj'
    , QUBO.isingExternalMagneticField = normalizeVec h'
    }
  , QUBO2IsingInfo c'
  )
  where
    {-
       Let xi = (si + 1)/2.

       Then,
         Qij xi xj
       = Qij (si + 1)/2 (sj + 1)/2
       = 1/4 Qij (si sj + si + sj + 1).

       Also,
         Qii xi xi
       = Qii (si + 1)/2 (si + 1)/2
       = 1/4 Qii (si si + 2 si + 1)
       = 1/4 Qii (2 si + 2).
    -}
    (jj', h', c') = foldl' f (IntMap.empty, IntMap.empty, 0) $ do
      (i, row)  <- IntMap.toList qq
      (j, q_ij) <- IntMap.toList row
      if i /= j then
        return
          ( IntMap.singleton (min i j) $ IntMap.singleton (max i j) q_ij
          , IntMap.fromList [(i,q_ij), (j,q_ij)]
          , q_ij
          )
      else
        return
          ( IntMap.empty
          , IntMap.singleton i (2 * q_ij)
          , 2 * q_ij
          )

    f (jj1, h1, c1) (jj2, h2, c2) =
      ( IntMap.unionWith (IntMap.unionWith (+)) jj1 jj2
      , IntMap.unionWith (+) h1 h2
      , c1+c2
      )

data QUBO2IsingInfo a = QUBO2IsingInfo a
  deriving (Eq, Show)

instance (Eq a, Show a) => Transformer (QUBO2IsingInfo a) where
  type Source (QUBO2IsingInfo a) = QUBO.Solution
  type Target (QUBO2IsingInfo a) = QUBO.Solution

instance (Eq a, Show a) => ForwardTransformer (QUBO2IsingInfo a) where
  transformForward _ sol = sol

instance (Eq a, Show a) => BackwardTransformer (QUBO2IsingInfo a) where
  transformBackward _ sol = sol

instance ObjValueTransformer (QUBO2IsingInfo a) where
  type SourceObjValue (QUBO2IsingInfo a) = a
  type TargetObjValue (QUBO2IsingInfo a) = a

instance (Eq a, Show a, Num a) => ObjValueForwardTransformer (QUBO2IsingInfo a) where
  transformObjValueForward (QUBO2IsingInfo offset) obj = 4 * obj - offset

-- XXX
instance (Eq a, Show a, Fractional a) => ObjValueBackwardTransformer (QUBO2IsingInfo a) where
  transformObjValueBackward (QUBO2IsingInfo offset) obj = (obj + offset) / 4

-- -----------------------------------------------------------------------------

ising2qubo :: (Eq a, Num a) => QUBO.IsingModel a -> (QUBO.Problem a, Ising2QUBOInfo a)
ising2qubo QUBO.IsingModel{ QUBO.isingNumVars = n, QUBO.isingInteraction = jj, QUBO.isingExternalMagneticField = h } =
  ( QUBO.Problem
    { QUBO.quboNumVars = n
    , QUBO.quboMatrix = mkMat m
    }
  , Ising2QUBOInfo offset
  )
  where
    {-
       Let si = 2 xi - 1

       Then,
         Jij si sj
       = Jij (2 xi - 1) (2 xj - 1)
       = Jij (4 xi xj - 2 xi - 2 xj + 1)
       = 4 Jij xi xj - 2 Jij xi    - 2 Jij xj    + Jij
       = 4 Jij xi xj - 2 Jij xi xi - 2 Jij xj xj + Jij

         hi si
       = hi (2 xi - 1)
       = 2 hi xi - hi
       = 2 hi xi xi - hi
    -}
    m =
      concat
      [ [(i, j, 4 * jj_ij), (i, i,  - 2 * jj_ij), (j, j,  - 2 * jj_ij)]
      | (i, row) <- IntMap.toList jj, (j, jj_ij) <- IntMap.toList row
      ] ++
      [ (i, i,  2 * hi) | (i, hi) <- IntMap.toList h ]
    offset =
        sum [jj_ij | row <- IntMap.elems jj, jj_ij <- IntMap.elems row]
      - sum (IntMap.elems h)

data Ising2QUBOInfo a = Ising2QUBOInfo a
  deriving (Eq, Show)

instance (Eq a, Show a) => Transformer (Ising2QUBOInfo a) where
  type Source (Ising2QUBOInfo a) = QUBO.Solution
  type Target (Ising2QUBOInfo a) = QUBO.Solution

instance (Eq a, Show a) => ForwardTransformer (Ising2QUBOInfo a) where
  transformForward _ sol = sol

instance (Eq a, Show a) => BackwardTransformer (Ising2QUBOInfo a) where
  transformBackward _ sol = sol

instance (Eq a, Show a) => ObjValueTransformer (Ising2QUBOInfo a) where
  type SourceObjValue (Ising2QUBOInfo a) = a
  type TargetObjValue (Ising2QUBOInfo a) = a

instance (Eq a, Show a, Num a) => ObjValueForwardTransformer (Ising2QUBOInfo a) where
  transformObjValueForward (Ising2QUBOInfo offset) obj = obj - offset

instance (Eq a, Show a, Num a) => ObjValueBackwardTransformer (Ising2QUBOInfo a) where
  transformObjValueBackward (Ising2QUBOInfo offset) obj = obj + offset

-- -----------------------------------------------------------------------------

mkMat :: (Eq a, Num a) => [(Int,Int,a)] -> IntMap (IntMap a)
mkMat m = normalizeMat $
  IntMap.unionsWith (IntMap.unionWith (+)) $
  [IntMap.singleton i (IntMap.singleton j qij) | (i,j,qij) <- m]

normalizeMat :: (Eq a, Num a) => IntMap (IntMap a) -> IntMap (IntMap a)
normalizeMat = IntMap.mapMaybe ((\m -> if IntMap.null m then Nothing else Just m) . normalizeVec)

normalizeVec :: (Eq a, Num a) => IntMap a -> IntMap a
normalizeVec = IntMap.filter (/=0)
