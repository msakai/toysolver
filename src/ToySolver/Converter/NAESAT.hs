{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.NAESAT
-- Copyright   :  (c) Masahiro Sakai 2018
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- Not-All-Equal SAT problems.
--
-----------------------------------------------------------------------------
module ToySolver.Converter.NAESAT
  (
  -- * Definition of NAE (Not-All-Equall) SAT problems.
    NAESAT
  , evalNAESAT
  , NAEClause
  , evalNAEClause

  -- * Conversion with SAT problem
  , SAT2NAESATInfo (..)
  , sat2naesat
  , NAESAT2SATInfo
  , naesat2sat

  -- * Conversion from general NAE-SAT to NAE-k-SAT
  , NAESAT2NAEKSATInfo (..)
  , naesat2naeksat

  -- ** NAE-SAT to MAX-2-SAT
  , NAESAT2Max2SATInfo
  , naesat2max2sat
  , NAE3SAT2Max2SATInfo
  , nae3sat2max2sat
  ) where

import Control.Monad.State.Strict
import Data.Array.Unboxed
import qualified Data.IntMap as IntMap
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Unboxed as VU
import ToySolver.Converter.Base
import qualified ToySolver.FileFormat.CNF as CNF
import qualified ToySolver.SAT.Types as SAT

type NAESAT = (Int, [NAEClause])

evalNAESAT :: SAT.IModel m => m -> NAESAT -> Bool
evalNAESAT m (_,cs) = all (evalNAEClause m) cs

type NAEClause = VU.Vector SAT.Lit

evalNAEClause :: SAT.IModel m => m -> NAEClause -> Bool
evalNAEClause m c =
  VG.any (SAT.evalLit m) c && VG.any (not . SAT.evalLit m) c

-- ------------------------------------------------------------------------

-- | Information of 'sat2naesat' conversion
newtype SAT2NAESATInfo = SAT2NAESATInfo SAT.Var
  deriving (Eq, Show, Read)

-- | Convert a CNF formula φ to an equisatifiable NAE-SAT formula ψ,
-- together with a 'SAT2NAESATInfo'
sat2naesat :: CNF.CNF -> (NAESAT, SAT2NAESATInfo)
sat2naesat cnf = (ret, SAT2NAESATInfo z)
  where
    z = CNF.cnfNumVars cnf + 1
    ret =
      ( CNF.cnfNumVars cnf + 1
      , [VG.snoc clause z | clause <- CNF.cnfClauses cnf]
      )

instance Transformer SAT2NAESATInfo where
  type Source SAT2NAESATInfo = SAT.Model
  type Target SAT2NAESATInfo = SAT.Model

instance ForwardTransformer SAT2NAESATInfo where
  transformForward (SAT2NAESATInfo z) m = array (1,z) $ (z,False) : assocs m

instance BackwardTransformer SAT2NAESATInfo where
  transformBackward (SAT2NAESATInfo z) m = 
    SAT.restrictModel (z - 1) $
      if SAT.evalVar m z then amap not m else m

-- | Information of 'naesat2sat' conversion
type NAESAT2SATInfo = IdentityTransformer SAT.Model

-- | Convert a NAE-SAT formula φ to an equisatifiable CNF formula ψ,
-- together with a 'NAESAT2SATInfo'
naesat2sat :: NAESAT -> (CNF.CNF, NAESAT2SATInfo)
naesat2sat (n,cs) =
  ( CNF.CNF
    { CNF.cnfNumVars = n
    , CNF.cnfNumClauses = length cs * 2
    , CNF.cnfClauses = concat [[c, VG.map negate c] | c <- cs]
    }
  , IdentityTransformer
  )

-- ------------------------------------------------------------------------

-- Information of 'naesat2naeksta' conversion
data NAESAT2NAEKSATInfo = NAESAT2NAEKSATInfo !Int !Int [(SAT.Var, NAEClause, NAEClause)]
  deriving (Eq, Show, Read)

naesat2naeksat :: Int -> NAESAT -> (NAESAT, NAESAT2NAEKSATInfo)
naesat2naeksat k _ | k < 3 = error "naesat2naeksat: k must be >=3"
naesat2naeksat k (n,cs) = ((n', cs'), NAESAT2NAEKSATInfo n n' (reverse table))
  where
    (cs',(n',table)) = flip runState (n,[]) $ do
      liftM concat $ forM cs $ \c -> do
        let go c' r =
              if VG.length c' <= k then do
                return  $ reverse (c' : r)
              else do
                let (cs1, cs2) = VG.splitAt (k - 1) c'
                (i, tbl) <- get
                let w = i+1
                seq w $ put (w, (w,cs1,cs2) : tbl)
                go (VG.cons (-w) cs2) (VG.snoc cs1 w : r)
        go c []

instance Transformer NAESAT2NAEKSATInfo where
  type Source NAESAT2NAEKSATInfo = SAT.Model
  type Target NAESAT2NAEKSATInfo = SAT.Model

instance ForwardTransformer NAESAT2NAEKSATInfo where
  transformForward (NAESAT2NAEKSATInfo _n1 n2 table) m =
    array (1,n2) (go (IntMap.fromList (assocs m)) table)
    where
      go im [] = IntMap.toList im
      go im ((w,cs1,cs2) : tbl) = go (IntMap.insert w val im) tbl
        where
          ev x
            | x > 0     = im IntMap.! x
            | otherwise = not $ im IntMap.! (- x)
          needTrue  = VG.all ev cs2 || VG.all (not . ev) cs1
          needFalse = VG.all ev cs1 || VG.all (not . ev) cs2
          val
            | needTrue && needFalse = True -- error "naesat2naeksat_forward: invalid model"
            | needTrue  = True
            | needFalse = False
            | otherwise = False

instance BackwardTransformer NAESAT2NAEKSATInfo where
  transformBackward (NAESAT2NAEKSATInfo n1 _n2 _table) = SAT.restrictModel n1

-- ------------------------------------------------------------------------

type NAESAT2Max2SATInfo = ComposedTransformer NAESAT2NAEKSATInfo NAE3SAT2Max2SATInfo

naesat2max2sat :: NAESAT -> ((CNF.WCNF, Integer), NAESAT2Max2SATInfo)
naesat2max2sat x = (x2, (ComposedTransformer info1 info2))
  where
    (x1, info1) = naesat2naeksat 3 x
    (x2, info2) = nae3sat2max2sat x1

-- ------------------------------------------------------------------------

type NAE3SAT2Max2SATInfo = IdentityTransformer SAT.Model

-- Original nae-sat problem is satisfiable iff MAX-2-SAT problem has solution with cost <=threshold.
nae3sat2max2sat :: NAESAT -> ((CNF.WCNF, Integer), NAE3SAT2Max2SATInfo)
nae3sat2max2sat (n,cs)
  | any (\c -> VG.length c < 2) cs =
      ( ( CNF.WCNF
          { CNF.wcnfTopCost = 2
          , CNF.wcnfNumVars = n
          , CNF.wcnfClauses = [(1, SAT.packClause [])]
          , CNF.wcnfNumClauses = 1
          }
        , 0
        )
      , IdentityTransformer
      )
  | otherwise =
      ( ( CNF.WCNF
          { CNF.wcnfTopCost = fromIntegral nc' + 1
          , CNF.wcnfNumVars = n
          , CNF.wcnfClauses = cs'
          , CNF.wcnfNumClauses = nc'
          }
        , t
        )
      , IdentityTransformer
      )
  where
    nc' = length cs'
    (cs', t) = foldl f ([],0) cs
      where
        f :: ([CNF.WeightedClause], Integer) -> VU.Vector SAT.Lit -> ([CNF.WeightedClause], Integer)
        f (cs, !t) c =
          case SAT.unpackClause c of
            []  -> error "nae3sat2max2sat: should not happen"
            [_] -> error "nae3sat2max2sat: should not happen"
            [_,_] ->
                ( [(1, c), (1, VG.map negate c)] ++ cs
                , t
                )
            [l0,l1,l2] ->
                ( concat [[(1, SAT.packClause [a,b]), (1, SAT.packClause [-a,-b])] | (a,b) <- [(l0,l1),(l1,l2),(l2,l0)]] ++ cs
                , t + 1
                )
            _ -> error "nae3sat2max2sat: cannot handle nae-clause of size >3"

-- ------------------------------------------------------------------------

