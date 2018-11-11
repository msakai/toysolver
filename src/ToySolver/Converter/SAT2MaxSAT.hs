{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeFamilies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Converter.SAT2MaxSAT
-- Copyright   :  (c) Masahiro Sakai 2018
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-----------------------------------------------------------------------------
module ToySolver.Converter.SAT2MaxSAT
  (
  -- * SAT to Max-2-SAT conversion
    SATToMaxSAT2Info
  , satToMaxSAT2

  -- * Low-level conversion

  -- ** 3-SAT to Max-2-SAT conversion
  , SAT3ToMaxSAT2Info (..)
  , sat3ToMaxSAT2
  ) where

import Control.Monad
import Data.Array.MArray
import Data.Array.ST
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.List
import qualified ToySolver.FileFormat.CNF as CNF
import ToySolver.Converter.Base
import ToySolver.Converter.SAT2KSAT
import qualified ToySolver.SAT.Types as SAT


type SATToMaxSAT2Info = ComposedTransformer SAT2KSATInfo SAT3ToMaxSAT2Info

satToMaxSAT2 :: CNF.CNF -> ((CNF.WCNF, Integer), SATToMaxSAT2Info)
satToMaxSAT2 x = (x2, (ComposedTransformer info1 info2))
  where
    (x1, info1) = sat2ksat 3 x
    (x2, info2) = sat3ToMaxSAT2 x1


sat3ToMaxSAT2 :: CNF.CNF -> ((CNF.WCNF, Integer), SAT3ToMaxSAT2Info)
sat3ToMaxSAT2 cnf =
  case foldl' f (CNF.cnfNumVars cnf, 0, [], [], 0) (CNF.cnfClauses cnf) of
    (!nv, !nc, !cs, ds, !t) ->
      ( ( CNF.WCNF
          { CNF.wcnfNumVars = nv
          , CNF.wcnfNumClauses = nc
          , CNF.wcnfTopCost = fromIntegral $ nc + 1
          , CNF.wcnfClauses = reverse cs
          }
        , t
        )
      , SAT3ToMaxSAT2Info (CNF.cnfNumVars cnf) nv (IntMap.fromList ds)
      )
  where
    f :: (Int, Int, [CNF.WeightedClause], [(SAT.Var,(SAT.Lit,SAT.Lit,SAT.Lit))], Integer)
      -> SAT.PackedClause
      -> (Int, Int, [CNF.WeightedClause], [(SAT.Var,(SAT.Lit,SAT.Lit,SAT.Lit))], Integer)
    f (!nv, !nc, cs, ds, t) clause =
      case SAT.unpackClause clause of
        []       -> (nv, nc+1, (1,clause) : cs, ds, t)
        [_a]     -> (nv, nc+1, (1,clause) : cs, ds, t)
        [_a, _b] -> (nv, nc+1, (1,clause) : cs, ds, t)
        [a, b, c] ->
          let d = nv+1
              cs2 = [[a], [b], [c], [d], [-a,-b], [-a,-c], [-b,-c], [a,-d], [b,-d], [c,-d]]
          in (nv+1, nc + length cs2, map (\clause' -> (1, SAT.packClause clause')) cs2 ++ cs, (d, (a,b,c)) : ds, t + 3)
        _ -> error "not a 3-SAT instance"

data SAT3ToMaxSAT2Info = SAT3ToMaxSAT2Info !Int !Int (IntMap (SAT.Lit,SAT.Lit,SAT.Lit))
  deriving (Eq, Ord, Show)

instance Transformer SAT3ToMaxSAT2Info where
  type Source SAT3ToMaxSAT2Info = SAT.Model
  type Target SAT3ToMaxSAT2Info = SAT.Model

instance ForwardTransformer SAT3ToMaxSAT2Info where
  transformForward (SAT3ToMaxSAT2Info nv1 nv2 ds) m = runSTUArray $ do
    m2 <- newArray_ (1,nv2)
    forM_ [1..nv1] $ \v -> do
      writeArray m2 v (SAT.evalVar m v)
    forM_ (IntMap.toList ds) $ \(d, (a,b,c)) -> do
      let n :: Int
          n = sum [1 | l <- [a,b,c], SAT.evalLit m l]
      writeArray m2 d $
        case n of
          1 -> False
          2 -> False -- True is also OK
          3 -> True
          _ -> False -- precondition is violated
    return m2

instance BackwardTransformer SAT3ToMaxSAT2Info where
  transformBackward (SAT3ToMaxSAT2Info nv1 _nv2 _ds) = SAT.restrictModel nv1
