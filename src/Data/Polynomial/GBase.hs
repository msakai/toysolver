{-# LANGUAGE ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Polynomial.GBase
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
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
-- * Polynomial class for Ruby <http://www.math.kobe-u.ac.jp/~kodama/tips-RubyPoly.html>
--
-- * Docon <http://www.haskell.org/docon/>
--
-- * constructive-algebra package <http://hackage.haskell.org/package/constructive-algebra>
-- 
-----------------------------------------------------------------------------

module Data.Polynomial.GBase
  (
  -- * Gröbner basis
    buchberger
  , spolynomial
  , reduceGBase
  ) where

import qualified Data.Set as Set
import Data.Polynomial

{--------------------------------------------------------------------
  Gröbner basis
--------------------------------------------------------------------}

spolynomial
  :: (Eq k, Fractional k, Ord v, Show v)
  => MonomialOrder v -> Polynomial k v -> Polynomial k v -> Polynomial k v
spolynomial cmp f g =
      fromMonomial ((1,xs) `monomialDiv` (c1,xs1)) * f
    - fromMonomial ((1,xs) `monomialDiv` (c2,xs2)) * g
  where
    xs = mmLCM xs1 xs2
    (c1, xs1) = leadingTerm cmp f
    (c2, xs2) = leadingTerm cmp g

buchberger
  :: forall k v. (Eq k, Fractional k, Ord k, Ord v, Show v)
  => MonomialOrder v -> [Polynomial k v] -> [Polynomial k v]
buchberger cmp fs = reduceGBase cmp $ go fs (pairs fs)
  where  
    go :: [Polynomial k v] -> [(Polynomial k v, Polynomial k v)] -> [Polynomial k v]
    go gs [] = gs
    go gs ((fi,fj):ps)
      | r == 0    = go gs ps
      | otherwise = go (r:gs) ([(r,g) | g <- gs] ++ ps)
      where
        spoly = spolynomial cmp fi fj
        r = reduce cmp spoly gs

reduceGBase
  :: forall k v. (Eq k, Ord k, Fractional k, Ord v, Show v)
  => MonomialOrder v -> [Polynomial k v] -> [Polynomial k v]
reduceGBase cmp ps = Set.toList $ Set.fromList $ go ps []
  where
    go [] qs = qs
    go (p:ps) qs
      | q == 0    = go ps qs
      | otherwise = go ps (constant (1/c) * q : qs)
      where
        q = reduce cmp p (ps++qs)
        (c,_) = leadingTerm cmp q

{--------------------------------------------------------------------
  Utilities
--------------------------------------------------------------------}

pairs :: [a] -> [(a,a)]
pairs [] = []
pairs (x:xs) = [(x,y) | y <- xs] ++ pairs xs
