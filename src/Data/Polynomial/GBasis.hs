{-# LANGUAGE ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Polynomial.GBasis
-- Copyright   :  (c) Masahiro Sakai 2012-2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (ScopedTypeVariables)
-- 
-- Gröbner basis
--
-- References:
--
-- * Monomial order <http://en.wikipedia.org/wiki/Monomial_order>
-- 
-- * Gröbner basis <http://en.wikipedia.org/wiki/Gr%C3%B6bner_basis>
--
-- * グレブナー基底 <http://d.hatena.ne.jp/keyword/%A5%B0%A5%EC%A5%D6%A5%CA%A1%BC%B4%F0%C4%EC>
--
-- * Gröbner Bases and Buchberger’s Algorithm <http://math.rice.edu/~cbruun/vigre/vigreHW6.pdf>
--
-- * Docon <http://www.haskell.org/docon/>
-- 
-----------------------------------------------------------------------------

module Data.Polynomial.GBasis
  (
  -- * Options
    Options (..)
  , Strategy (..)
  , defaultOptions

  -- * Gröbner basis computation
  , basis
  , basis'
  , spolynomial
  , reduceGBasis
  ) where

import qualified Data.Set as Set
import qualified Data.Heap as H -- http://hackage.haskell.org/package/heaps
import Data.Polynomial

data Options
  = Options
  { optStrategy :: Strategy
  }

defaultOptions :: Options
defaultOptions =
  Options
  { optStrategy = NormalStrategy
  }

data Strategy
  = NormalStrategy
  | SugarStrategy  -- ^ sugar strategy (not implemented yet)
  deriving (Eq, Ord, Show, Read, Bounded, Enum)

spolynomial
  :: (Eq k, Fractional k, Ord v)
  => MonomialOrder v -> Polynomial k v -> Polynomial k v -> Polynomial k v
spolynomial cmp f g =
      fromTerm ((1,xs) `tdiv` lt1) * f
    - fromTerm ((1,xs) `tdiv` lt2) * g
  where
    xs = mlcm xs1 xs2
    lt1@(c1, xs1) = lt cmp f
    lt2@(c2, xs2) = lt cmp g

basis
  :: forall k v. (Eq k, Fractional k, Ord k, Ord v)
  => MonomialOrder v
  -> [Polynomial k v]
  -> [Polynomial k v]
basis = basis' defaultOptions

basis'
  :: forall k v. (Eq k, Fractional k, Ord k, Ord v)
  => Options
  -> MonomialOrder v
  -> [Polynomial k v]
  -> [Polynomial k v]
basis' opt cmp fs =
  reduceGBasis cmp $ go fs (H.fromList [item cmp fi fj | (fi,fj) <- pairs fs, checkGCD fi fj])
  where
    go :: [Polynomial k v] -> H.Heap (Item k v) -> [Polynomial k v]
    go gs h | H.null h = gs
    go gs h
      | r == 0    = go gs h'
      | otherwise = go (r:gs) (H.union h' (H.fromList [item cmp r g | g <- gs, checkGCD fi fj]))
      where
        Just (i, h') = H.viewMin h
        fi = iFst i
        fj = iSnd i
        spoly = spolynomial cmp fi fj
        r = reduce cmp spoly gs

    -- gcdが1となる組は選ばなくて良い
    checkGCD fi fj = mgcd (lm cmp fi) (lm cmp fj) /= mone

reduceGBasis
  :: forall k v. (Eq k, Ord k, Fractional k, Ord v)
  => MonomialOrder v -> [Polynomial k v] -> [Polynomial k v]
reduceGBasis cmp ps = Set.toList $ Set.fromList $ go ps []
  where
    go [] qs = qs
    go (p:ps) qs
      | q == 0    = go ps qs
      | otherwise = go ps (toMonic cmp q : qs)
      where
        q = reduce cmp p (ps++qs)

{--------------------------------------------------------------------
  Item
--------------------------------------------------------------------}

data Item k v
  = Item
  { iFst :: Polynomial k v
  , iSnd :: Polynomial k v
  , iCmp :: MonomialOrder v
  , iLCM :: Monomial v
  }

item :: (Eq k, Num k, Ord v) => MonomialOrder v -> Polynomial k v -> Polynomial k v -> Item k v
item cmp f g = Item f g cmp (mlcm (lm cmp f) (lm cmp g))

instance Ord v => Ord (Item k v) where
  a `compare` b = iCmp a (iLCM a) (iLCM b)

instance Ord v => Eq (Item k v) where
  a == b = compare a b == EQ

{--------------------------------------------------------------------
  Utilities
--------------------------------------------------------------------}

pairs :: [a] -> [(a,a)]
pairs [] = []
pairs (x:xs) = [(x,y) | y <- xs] ++ pairs xs
