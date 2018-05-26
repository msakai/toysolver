{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
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
  , SAT2NAESATInfo
  , sat2naesat
  , sat2naesat_forward
  , sat2naesat_backward
  , NAESAT2SATInfo
  , naesat2sat
  , naesat2sat_forward
  , naesat2sat_backward

  -- * Conversion from general NAE-SAT to NAE-k-SAT
  , NAESAT2NAEKSATInfo
  , naesat2naeksat
  , naesat2naeksat_forward
  , naesat2naeksat_backward
  ) where

import Control.Monad.State.Strict
import Data.Array.Unboxed
import qualified Data.IntMap as IntMap
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Unboxed as VU
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.Text.CNF as CNF

type NAESAT = (Int, [NAEClause])

evalNAESAT :: SAT.IModel m => m -> NAESAT -> Bool
evalNAESAT m (_,cs) = all (evalNAEClause m) cs

type NAEClause = VU.Vector SAT.Lit

evalNAEClause :: SAT.IModel m => m -> NAEClause -> Bool
evalNAEClause m c =
  VG.any (SAT.evalLit m) c && VG.any (not . SAT.evalLit m) c

-- ------------------------------------------------------------------------

-- | Information for 'sat2naesat_forward' and 'sat2naesat_backward'.
type SAT2NAESATInfo = SAT.Var

-- | Convert a CNF formula φ to an equisatifiable NAE-SAT formula ψ,
-- together with a 'SAT2NAESATInfo'
sat2naesat :: CNF.CNF -> (NAESAT, SAT2NAESATInfo)
sat2naesat cnf = (ret, z)
  where
    z = CNF.cnfNumVars cnf + 1
    ret =
      ( CNF.cnfNumVars cnf + 1
      , [VG.snoc clause z | clause <- CNF.cnfClauses cnf]
      )

-- | Suppose @(ψ, info) = 'sat2naesat' φ@, @sat2naesat_forward@ transform
-- a model of φ to a model of ψ.
sat2naesat_forward :: SAT2NAESATInfo -> SAT.Model -> SAT.Model
sat2naesat_forward z m = array (1,z) $ (z,False) : assocs m

-- | Suppose @(ψ, info) = 'sat2naesat' φ@, @sat2naesat_forward@ transform
-- a model of ψ to a model of φ.
sat2naesat_backward :: SAT2NAESATInfo -> SAT.Model -> SAT.Model
sat2naesat_backward z m =
  SAT.restrictModel (z - 1) $
    if SAT.evalVar m z then amap not m else m

-- | Information for 'naesat2sat_forward' and 'naesat2sat_backward'.
type NAESAT2SATInfo = ()

-- | Convert a NAE-SAT formula φ to an equisatifiable CNF formula ψ,
-- together with a 'NAESAT2SATInfo'
naesat2sat :: NAESAT -> (CNF.CNF, NAESAT2SATInfo)
naesat2sat (n,cs) =
  ( CNF.CNF
    { CNF.cnfNumVars = n
    , CNF.cnfNumClauses = length cs * 2
    , CNF.cnfClauses = concat [[c, VG.map negate c] | c <- cs]
    }
  , ()
  )

-- | Suppose @(ψ, info) = 'naesat2sat' φ@, @naesat2sat_forward@ transform
-- a model of φ to a model of ψ.
naesat2sat_forward :: NAESAT2SATInfo -> SAT.Model -> SAT.Model
naesat2sat_forward () = id

-- | Suppose @(ψ, info) = 'naesat2sat' φ@, @naesat2sat_forward@ transform
-- a model of ψ to a model of φ.
naesat2sat_backward :: NAESAT2SATInfo -> SAT.Model -> SAT.Model
naesat2sat_backward () = id

-- ------------------------------------------------------------------------

type NAESAT2NAEKSATInfo = (Int, Int, [(SAT.Var, NAEClause, NAEClause)])

naesat2naeksat :: Int -> NAESAT -> (NAESAT, NAESAT2NAEKSATInfo)
naesat2naeksat k _ | k < 3 = error "naesat2naeksat: k must be >=3"
naesat2naeksat k (n,cs) = ((n', cs'), (n, n', reverse table))
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

naesat2naeksat_forward :: NAESAT2NAEKSATInfo -> SAT.Model -> SAT.Model
naesat2naeksat_forward (_n1,n2,table) m = array (1,n2) (go (IntMap.fromList (assocs m)) table)
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

naesat2naeksat_backward :: NAESAT2NAEKSATInfo -> SAT.Model -> SAT.Model
naesat2naeksat_backward (n1,_,_) m = SAT.restrictModel n1 m

-- ------------------------------------------------------------------------
