{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
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
-- References:
--
-- * M. R. Garey, D. S. Johnson, and L. Stockmeyer. Some simplified NP-complete
--   problems. In STOC ’74: Proceedings of the sixth annual ACM symposium on Theory
--   of computing, pages 47–63, New York, NY, USA, 1974.
--   https://dl.acm.org/citation.cfm?doid=800119.803884
--   https://www.sciencedirect.com/science/article/pii/0304397576900591
--
-----------------------------------------------------------------------------
module ToySolver.Converter.SAT2MaxSAT
  (
  -- * SAT to Max-2-SAT conversion
    SATToMaxSAT2Info
  , satToMaxSAT2

  -- * Max-2-SAT to simple Max-Cut conversion
  , MaxSAT2ToSimpleMaxCutInfo
  , maxSAT2ToSimpleMaxCut

  -- * SAT to simple Max-Cut conversion
  , SATToSimpleMaxCutInfo
  , satToSimpleMaxCut

  -- * Low-level conversion

  -- ** 3-SAT to Max-2-SAT conversion
  , SAT3ToMaxSAT2Info
  , sat3ToMaxSAT2

  -- ** Max-2-SAT to SimpleMaxSAT2 conversion
  , SimpleMaxSAT2
  , SimplifyMaxSAT2Info (..)
  , simplifyMaxSAT2

  -- ** SimpleMaxSAT2 to simple Max-Cut conversion
  , SimpleMaxSAT2ToSimpleMaxCutInfo (..)
  , simpleMaxSAT2ToSimpleMaxCut
  ) where

import Control.Monad
import Data.Array.MArray
import Data.Array.ST
import Data.Array.Unboxed
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import Data.List hiding (insert)
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import qualified ToySolver.FileFormat.CNF as CNF
import ToySolver.Converter.Base
import ToySolver.Converter.SAT2KSAT
import ToySolver.Converter.Tseitin
import ToySolver.Graph.Base
import qualified ToySolver.Graph.MaxCut as MaxCut
import qualified ToySolver.SAT.Types as SAT
import qualified ToySolver.SAT.Formula as SAT

-- ------------------------------------------------------------------------

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
      , TseitinInfo (CNF.cnfNumVars cnf) nv
          [ (d, SAT.And [SAT.Atom a, SAT.Atom b, SAT.Atom c])
            -- we define d as "a && b && c", but "a + b + c >= 2" is also fine.
          | (d, (a,b,c)) <- ds
          ]
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

type SAT3ToMaxSAT2Info = TseitinInfo

-- ------------------------------------------------------------------------

type MaxSAT2ToSimpleMaxCutInfo = ComposedTransformer SimplifyMaxSAT2Info SimpleMaxSAT2ToSimpleMaxCutInfo

maxSAT2ToSimpleMaxCut :: (CNF.WCNF, Integer) -> ((MaxCut.Problem Integer, Integer), MaxSAT2ToSimpleMaxCutInfo)
maxSAT2ToSimpleMaxCut x = (x2, (ComposedTransformer info1 info2))
  where
    (x1, info1) = simplifyMaxSAT2 x
    (x2, info2) = simpleMaxSAT2ToSimpleMaxCut x1

-- ------------------------------------------------------------------------

type SimpleMaxSAT2 = (Int, Set (Int, Int), Integer)

simplifyMaxSAT2 :: (CNF.WCNF, Integer) -> (SimpleMaxSAT2, SimplifyMaxSAT2Info)
simplifyMaxSAT2 (wcnf, threshold) =
  case foldl' f (nv1, Set.empty, IntMap.empty, threshold) (CNF.wcnfClauses wcnf) of
    (nv2, cs, defs, threshold2) -> ((nv2, cs, threshold2), SimplifyMaxSAT2Info nv1 nv2 defs)
  where
    nv1 = CNF.wcnfNumVars wcnf
    f r@(nv, cs, defs, t) (w, clause) =
      case SAT.unpackClause clause of
        []    -> (nv, cs, defs, t-w)
        [a]   -> applyN w (insert (a,a)) r
        [a,b] -> applyN w (insert (min a b, max a b)) r
        _ -> error "should not happen"
    insert c@(a,b) (nv,cs,defs,t)
      | c `Set.member` cs = (v, Set.insert (a,v) $ Set.insert (b,-v) cs, IntMap.insert v (a,b) defs, t)
      | otherwise         = (nv, Set.insert c cs, defs, t)
      where
        v = nv + 1

applyN :: Integral n => n -> (a -> a) -> (a -> a)
applyN n f = appEndo $ mconcat $ genericReplicate n (Endo f)

data SimplifyMaxSAT2Info
  = SimplifyMaxSAT2Info !Int !Int (IntMap (SAT.Lit, SAT.Lit))
  deriving (Eq, Show, Read)

instance Transformer SimplifyMaxSAT2Info where
  type Source SimplifyMaxSAT2Info = SAT.Model
  type Target SimplifyMaxSAT2Info = SAT.Model

instance ForwardTransformer SimplifyMaxSAT2Info where
  transformForward (SimplifyMaxSAT2Info _nv1 nv2 defs) m =
    array (1,nv2) $ assocs m ++ [(v, if SAT.evalLit m a then False else True) | (v,(a,_b)) <- IntMap.toList defs]

instance BackwardTransformer SimplifyMaxSAT2Info where
  transformBackward (SimplifyMaxSAT2Info nv1 _nv2 _defs) m = SAT.restrictModel nv1 m

-- ------------------------------------------------------------------------

simpleMaxSAT2ToSimpleMaxCut
  :: SimpleMaxSAT2
  -> ( (MaxCut.Problem Integer, Integer)
     , SimpleMaxSAT2ToSimpleMaxCutInfo
     )
simpleMaxSAT2ToSimpleMaxCut (n, cs, threshold) =
  ( ( graphFromUnorderedEdgesWith (+) numNodes [(a,b,1) | (a,b) <- (basicFramework ++ additionalEdges)]
    , w
    )
  , SimpleMaxSAT2ToSimpleMaxCutInfo n p
  )
  where
    p = Set.size cs
    (numNodes, tt, ff, t, f ,xp, xn, l) = simpleMaxSAT2ToSimpleMaxCutNodes n p

    basicFramework =
      [(tt i, ff j)   | i <- [0..3*p], j <- [0..3*p]] ++
      [(t i j, f i j) | i <- [1..n],   j <- [0..3*p]] ++
      [(xp i,  f i j) | i <- [1..n],   j <- [0..3*p]] ++
      [(xn i,  t i j) | i <- [1..n],   j <- [0..3*p]]
    sizeOfBasicFramework = (3*p+1)^(2::Int) + 3 * n*(3*p+1)

    additionalEdges =
      [ (l a, l b) | (a,b) <- Set.toList cs, a /= b ] ++
      [ (l a, ff (2*i-1)) | (i, (a,_b)) <- zip [1..] (Set.toList cs) ] ++
      [ (l b, ff (2*i  )) | (i, (_a,b)) <- zip [1..] (Set.toList cs) ]

    k = fromIntegral (Set.size cs) - threshold
    w = fromIntegral sizeOfBasicFramework + 2*k


simpleMaxSAT2ToSimpleMaxCutNodes
  :: Int -> Int
  -> ( Int
     , Int -> Int
     , Int -> Int
     , SAT.Var -> Int -> Int
     , SAT.Var -> Int -> Int
     , SAT.Var -> Int
     , SAT.Var -> Int
     , SAT.Lit -> Int
     )
simpleMaxSAT2ToSimpleMaxCutNodes n p = (numNodes, tt, ff, t, f ,xp, xn, l)
  where
    numNodes = (3*p+1) + (3*p+1) + n*(3*p+1) + n*(3*p+1) + n + n
    tt i  =                                                 i
    ff i  = (3*p+1) +                                       i
    t i j = (3*p+1) + (3*p+1) +                             (i-1)*(3*p+1) + j
    f i j = (3*p+1) + (3*p+1) + n*(3*p+1) +                 (i-1)*(3*p+1) + j
    xp i  = (3*p+1) + (3*p+1) + n*(3*p+1) + n*(3*p+1) +     (i-1)
    xn i  = (3*p+1) + (3*p+1) + n*(3*p+1) + n*(3*p+1) + n + (i-1)
    l x   = if x > 0 then xp x else xn (- x)


data SimpleMaxSAT2ToSimpleMaxCutInfo
  = SimpleMaxSAT2ToSimpleMaxCutInfo !Int !Int
  deriving (Eq, Show, Read)

instance Transformer SimpleMaxSAT2ToSimpleMaxCutInfo where
  type Source SimpleMaxSAT2ToSimpleMaxCutInfo = SAT.Model
  type Target SimpleMaxSAT2ToSimpleMaxCutInfo = MaxCut.Solution

instance ForwardTransformer SimpleMaxSAT2ToSimpleMaxCutInfo where
  transformForward (SimpleMaxSAT2ToSimpleMaxCutInfo n p) m =
    array (0,numNodes-1) [(v, not (v `IntSet.member` s1)) | v <- [0..numNodes-1]]
    where
      (numNodes, _tt, ff, t, f ,xp, xn, _l) = simpleMaxSAT2ToSimpleMaxCutNodes n p
      s1 = IntSet.fromList $
           [ff i  | i <- [0..3*p]] ++
           [xp i  | i <- [1..n], not (SAT.evalVar m i)] ++
           [t i j | i <- [1..n], not (SAT.evalVar m i), j <- [0..3*p]] ++
           [xn i  | i <- [1..n], SAT.evalVar m i] ++
           [f i j | i <- [1..n], SAT.evalVar m i, j <- [0..3*p]]

instance BackwardTransformer SimpleMaxSAT2ToSimpleMaxCutInfo where
  transformBackward (SimpleMaxSAT2ToSimpleMaxCutInfo n p) sol
    | p == 0    = array (1,n) [(i, False) | i <- [1..n]]
    | otherwise = array (1,n) [(i, (sol ! xp i) == b) | i <- [1..n]]
    where
      (_numNodes, _tt, ff, _t, _f ,xp, _xn, _l) = simpleMaxSAT2ToSimpleMaxCutNodes n p
      b = not (sol ! ff 0)

-- ------------------------------------------------------------------------

type SATToSimpleMaxCutInfo = ComposedTransformer SATToMaxSAT2Info MaxSAT2ToSimpleMaxCutInfo

satToSimpleMaxCut :: CNF.CNF -> ((MaxCut.Problem Integer, Integer), SATToSimpleMaxCutInfo)
satToSimpleMaxCut x = (x2, (ComposedTransformer info1 info2))
  where
    (x1, info1) = satToMaxSAT2 x
    (x2, info2) = maxSAT2ToSimpleMaxCut x1

-- ------------------------------------------------------------------------

