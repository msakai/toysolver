{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.QUBO
-- Copyright   :  (c) Masahiro Sakai 2018
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.Converter.QUBO
  ( qubo2pb
  , QUBO2PBInfo (..)

  , pb2qubo
  , PB2QUBOInfo

  , pbAsQUBO
  , PBAsQUBOInfo (..)

  , qubo2ising
  , QUBO2IsingInfo (..)

  , ising2qubo
  , Ising2QUBOInfo (..)
  ) where

import Control.Monad
import Control.Monad.State
import qualified Data.Aeson as J
import Data.Aeson ((.=), (.:))
import Data.Array.Unboxed
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.List
import Data.Maybe
import qualified Data.PseudoBoolean as PBFile
import Data.Ratio
import ToySolver.Converter.Base
import ToySolver.Converter.PB (pb2qubo', PB2QUBOInfo')
import ToySolver.Internal.JSON (withTypedObject)
import qualified ToySolver.QUBO as QUBO
import qualified ToySolver.SAT.Types as SAT

-- -----------------------------------------------------------------------------

qubo2pb :: Real a => QUBO.Problem a -> (PBFile.Formula, QUBO2PBInfo a)
qubo2pb prob =
  ( PBFile.Formula
    { PBFile.pbObjectiveFunction = Just $
        [ (c, if x1==x2 then [x1+1] else [x1+1, x2+1])
        | (x1, row) <- IntMap.toList m2
        , (x2, c) <- IntMap.toList row
        ]
    , PBFile.pbConstraints = []
    , PBFile.pbNumVars = QUBO.quboNumVars prob
    , PBFile.pbNumConstraints = 0
    }
  , QUBO2PBInfo d
  )
  where
    m1 = fmap (fmap toRational) $ QUBO.quboMatrix prob
    d = foldl' lcm 1 [denominator c | row <- IntMap.elems m1, c <- IntMap.elems row, c /= 0]
    m2 = fmap (fmap (\c -> numerator c * (d ` div` denominator c))) m1

newtype QUBO2PBInfo a = QUBO2PBInfo Integer
  deriving (Eq, Show, Read)

instance (Eq a, Show a, Read a) => Transformer (QUBO2PBInfo a) where
  type Source (QUBO2PBInfo a) = QUBO.Solution
  type Target (QUBO2PBInfo a) = SAT.Model

instance (Eq a, Show a, Read a) => ForwardTransformer (QUBO2PBInfo a) where
  transformForward (QUBO2PBInfo _) sol = ixmap (lb+1,ub+1) (subtract 1) sol
    where
      (lb,ub) = bounds sol

instance (Eq a, Show a, Read a) => BackwardTransformer (QUBO2PBInfo a) where
  transformBackward (QUBO2PBInfo _) m = ixmap (lb-1,ub-1) (+1) m
    where
      (lb,ub) = bounds m

instance (Eq a, Show a, Read a) => ObjValueTransformer (QUBO2PBInfo a) where
  type SourceObjValue (QUBO2PBInfo a) = a
  type TargetObjValue (QUBO2PBInfo a) = Integer

instance (Eq a, Show a, Read a, Real a) => ObjValueForwardTransformer (QUBO2PBInfo a) where
  transformObjValueForward (QUBO2PBInfo d) obj = round (toRational obj) * d

instance (Eq a, Show a, Read a, Num a) => ObjValueBackwardTransformer (QUBO2PBInfo a) where
  transformObjValueBackward (QUBO2PBInfo d) obj = fromInteger $ (obj + d - 1) `div` d

instance J.ToJSON (QUBO2PBInfo a) where
  toJSON (QUBO2PBInfo d) =
    J.object
    [ "type" .= J.String "QUBO2PBInfo"
    , "objective_function_scale_factor" .= d
    ]

instance J.FromJSON (QUBO2PBInfo a) where
  parseJSON =
    withTypedObject "QUBO2PBInfo" $ \obj ->
      QUBO2PBInfo <$> obj .: "objective_function_scale_factor"

-- -----------------------------------------------------------------------------

pbAsQUBO :: forall a. Real a => PBFile.Formula -> Maybe (QUBO.Problem a, PBAsQUBOInfo a)
pbAsQUBO formula = do
  (prob, offset) <- runStateT body 0
  return $ (prob, PBAsQUBOInfo offset)
  where
    body :: StateT Integer Maybe (QUBO.Problem a)
    body = do
      guard $ null (PBFile.pbConstraints formula)
      let f :: PBFile.WeightedTerm -> StateT Integer Maybe [(Integer, Int, Int)]
          f (c,[]) = modify (subtract c) >> return []
          f (c,[x]) = return [(c,x,x)]
          f (c,[x1,x2]) = return [(c,x1,x2)]
          f _ = mzero
      xs <- mapM f $ SAT.removeNegationFromPBSum $ fromMaybe [] $ PBFile.pbObjectiveFunction formula
      return $
        QUBO.Problem
        { QUBO.quboNumVars = PBFile.pbNumVars formula
        , QUBO.quboMatrix = mkMat $
            [ (x1', x2', fromInteger c)
            | (c,x1,x2) <- concat xs, let x1' = min x1 x2 - 1, let x2' = max x1 x2 - 1
            ]
        }

data PBAsQUBOInfo a = PBAsQUBOInfo !Integer
  deriving (Eq, Show, Read)

instance Transformer (PBAsQUBOInfo a) where
  type Source (PBAsQUBOInfo a) = SAT.Model
  type Target (PBAsQUBOInfo a) = QUBO.Solution

instance ForwardTransformer (PBAsQUBOInfo a) where
  transformForward (PBAsQUBOInfo _offset) m = ixmap (lb-1,ub-1) (+1) m
    where
      (lb,ub) = bounds m

instance BackwardTransformer (PBAsQUBOInfo a) where
  transformBackward (PBAsQUBOInfo _offset) sol = ixmap (lb+1,ub+1) (subtract 1) sol
    where
      (lb,ub) = bounds sol

instance ObjValueTransformer (PBAsQUBOInfo a) where
  type SourceObjValue (PBAsQUBOInfo a) = Integer
  type TargetObjValue (PBAsQUBOInfo a) = a

instance Num a => ObjValueForwardTransformer (PBAsQUBOInfo a) where
  transformObjValueForward (PBAsQUBOInfo offset) obj = fromInteger (obj + offset)

instance Real a => ObjValueBackwardTransformer (PBAsQUBOInfo a) where
  transformObjValueBackward (PBAsQUBOInfo offset) obj = round (toRational obj) - offset

instance J.ToJSON (PBAsQUBOInfo a) where
  toJSON (PBAsQUBOInfo offset) =
    J.object
    [ "type" .= J.String "PBAsQUBOInfo"
    , "objective_function_offset" .= offset
    ]

instance J.FromJSON (PBAsQUBOInfo a) where
  parseJSON =
    withTypedObject "PBAsQUBOInfo" $ \obj -> do
      offset <- obj .: "objective_function_offset"
      pure (PBAsQUBOInfo offset)

-- -----------------------------------------------------------------------------

pb2qubo :: Real a => PBFile.Formula -> ((QUBO.Problem a, a), PB2QUBOInfo a)
pb2qubo formula = ((qubo, transformObjValueForward info2 th), ComposedTransformer info1 info2)
  where
    ((qubo', th), info1) = pb2qubo' formula
    Just (qubo, info2) = pbAsQUBO qubo'

type PB2QUBOInfo a = ComposedTransformer PB2QUBOInfo' (PBAsQUBOInfo a)

-- -----------------------------------------------------------------------------

qubo2ising :: (Eq a, Show a, Fractional a) => QUBO.Problem a -> (QUBO.IsingModel a, QUBO2IsingInfo a)
qubo2ising QUBO.Problem{ QUBO.quboNumVars = n, QUBO.quboMatrix = qq } =
  ( QUBO.IsingModel
    { QUBO.isingNumVars = n
    , QUBO.isingInteraction = normalizeMat $ jj'
    , QUBO.isingExternalMagneticField = normalizeVec h'
    }
  , QUBO2IsingInfo (- c')
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
          ( IntMap.singleton (min i j) $ IntMap.singleton (max i j) (q_ij / 4)
          , IntMap.fromList [(i, q_ij / 4), (j, q_ij / 4)]
          , q_ij / 4
          )
      else
        return
          ( IntMap.empty
          , IntMap.singleton i (q_ij / 2)
          , q_ij / 2
          )

    f (jj1, h1, c1) (jj2, h2, c2) =
      ( IntMap.unionWith (IntMap.unionWith (+)) jj1 jj2
      , IntMap.unionWith (+) h1 h2
      , c1+c2
      )

data QUBO2IsingInfo a = QUBO2IsingInfo a
  deriving (Eq, Show, Read)

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
  transformObjValueForward (QUBO2IsingInfo offset) obj = obj + offset

instance (Eq a, Show a, Num a) => ObjValueBackwardTransformer (QUBO2IsingInfo a) where
  transformObjValueBackward (QUBO2IsingInfo offset) obj = obj - offset

instance J.ToJSON a => J.ToJSON (QUBO2IsingInfo a) where
  toJSON (QUBO2IsingInfo offset) =
    J.object
    [ "type" .= J.String "QUBO2IsingInfo"
    , "objective_function_offset" .= offset
    ]

instance J.FromJSON a => J.FromJSON (QUBO2IsingInfo a) where
  parseJSON =
    withTypedObject "QUBO2IsingInfo" $ \obj -> do
      offset <- obj .: "objective_function_offset"
      pure (QUBO2IsingInfo offset)

-- -----------------------------------------------------------------------------

ising2qubo :: (Eq a, Num a) => QUBO.IsingModel a -> (QUBO.Problem a, Ising2QUBOInfo a)
ising2qubo QUBO.IsingModel{ QUBO.isingNumVars = n, QUBO.isingInteraction = jj, QUBO.isingExternalMagneticField = h } =
  ( QUBO.Problem
    { QUBO.quboNumVars = n
    , QUBO.quboMatrix = mkMat m
    }
  , Ising2QUBOInfo (- offset)
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
  deriving (Eq, Show, Read)

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
  transformObjValueForward (Ising2QUBOInfo offset) obj = obj + offset

instance (Eq a, Show a, Num a) => ObjValueBackwardTransformer (Ising2QUBOInfo a) where
  transformObjValueBackward (Ising2QUBOInfo offset) obj = obj - offset

instance J.ToJSON a => J.ToJSON (Ising2QUBOInfo a) where
  toJSON (Ising2QUBOInfo offset) =
    J.object
    [ "type" .= J.String "Ising2QUBOInfo"
    , "objective_function_offset" .= offset
    ]

instance J.FromJSON a => J.FromJSON (Ising2QUBOInfo a) where
  parseJSON =
    withTypedObject "Ising2QUBOInfo" $ \obj -> do
      offset <- obj .: "objective_function_offset"
      pure (Ising2QUBOInfo offset)

-- -----------------------------------------------------------------------------

mkMat :: (Eq a, Num a) => [(Int,Int,a)] -> IntMap (IntMap a)
mkMat m = normalizeMat $
  IntMap.unionsWith (IntMap.unionWith (+)) $
  [IntMap.singleton i (IntMap.singleton j qij) | (i,j,qij) <- m]

normalizeMat :: (Eq a, Num a) => IntMap (IntMap a) -> IntMap (IntMap a)
normalizeMat = IntMap.mapMaybe ((\m -> if IntMap.null m then Nothing else Just m) . normalizeVec)

normalizeVec :: (Eq a, Num a) => IntMap a -> IntMap a
normalizeVec = IntMap.filter (/=0)
