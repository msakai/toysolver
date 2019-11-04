{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.AlgebraicNumber.Root
-- Copyright   :  (c) Masahiro Sakai 2012-2016
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- Manipulating polynomials for corresponding operations for algebraic numbers.
-- 
-- Reference:
--
-- * <http://www.dpmms.cam.ac.uk/~wtg10/galois.html>
-- 
-----------------------------------------------------------------------------
module ToySolver.Data.AlgebraicNumber.Root where

import Data.List
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set

import ToySolver.Data.Polynomial (Polynomial, UPolynomial, X (..))
import qualified ToySolver.Data.Polynomial as P
import qualified ToySolver.Data.Polynomial.GroebnerBasis as GB

type Var = Int

{--------------------------------------------------------------------
  Manipulation of polynomials
--------------------------------------------------------------------}

normalizePoly :: (Fractional k, Eq k) => UPolynomial k -> UPolynomial k
normalizePoly = P.toMonic P.nat

rootAdd :: (Fractional k, Ord k) => UPolynomial k -> UPolynomial k -> UPolynomial k
rootAdd p1 p2 = lift2 (+) p1 p2

rootMul :: (Fractional k, Ord k) => UPolynomial k -> UPolynomial k -> UPolynomial k
rootMul p1 p2 = lift2 (*) p1 p2

rootShift :: (Fractional k, Eq k) => k -> UPolynomial k -> UPolynomial k
rootShift 0 p = p
rootShift r p = normalizePoly $ P.subst p (\X -> P.var X - P.constant r)

rootScale :: (Fractional k, Eq k) => k -> UPolynomial k -> UPolynomial k
rootScale 0 p = P.var X
rootScale r p = normalizePoly $ P.subst p (\X -> P.constant (recip r) * P.var X)

rootRecip :: (Fractional k, Eq k) => UPolynomial k -> UPolynomial k
rootRecip p = normalizePoly $ P.fromTerms [(c, P.var X `P.mpow` (d - P.deg xs)) | (c, xs) <- P.terms p]
  where
    d = P.deg p

-- | Given a polynomial P = Σ_i a_i x^i over L/K where each a_i is a root of polynomial @f a_i@ over K,
-- @rootSimpPoly f P@ computes a polynomial Q over K such that roots of P is a subset of roots of Q.
rootSimpPoly :: forall k l. (Fractional k, Ord k) => (l -> UPolynomial k) -> UPolynomial l -> UPolynomial k
rootSimpPoly f p = findPoly (P.var 0) ps
  where
    ys :: [(UPolynomial k, Var)]
    ys = zip (Set.toAscList $ Set.fromList [f c | (c, _) <- P.terms p]) [1..]

    m :: Map (UPolynomial k) Var
    m = Map.fromDistinctAscList ys

    p' :: Polynomial k Var
    p' = P.eval (\X -> P.var 0) (P.mapCoeff (\c -> P.var (m Map.! (f c))) p)

    ps :: [Polynomial k Var]
    ps = p' : [P.subst q (\X -> P.var x) | (q, x) <- ys]

rootNthRoot :: (Fractional k, Ord k) => Integer -> UPolynomial k -> UPolynomial k
rootNthRoot n p = P.subst p (\X -> (P.var X)^n)

lift2 :: forall k. (Fractional k, Ord k) => (forall a. Num a => a -> a -> a)
      -> UPolynomial k -> UPolynomial k -> UPolynomial k
lift2 f p1 p2 = findPoly f_a_b gbase
  where
    a, b :: Var
    a = 0
    b = 1

    f_a_b :: Polynomial k Var
    f_a_b = f (P.var a) (P.var b)

    gbase :: [Polynomial k Var]
    gbase = [ P.subst p1 (\X -> P.var a), P.subst p2 (\X -> P.var b) ]

-- | Given a polynomial P and polynomials {P1,…,Pn} over K,
-- findPoly P [P1..Pn] computes a non-zero polynomial Q such that Q[P] = 0 modulo {P1,…,Pn}.
findPoly :: forall k. (Fractional k, Ord k) => Polynomial k Var -> [Polynomial k Var] -> UPolynomial k
findPoly c ps = normalizePoly $ sum [P.constant coeff * (P.var X) ^ n | (n,coeff) <- zip [0..] coeffs]
  where  
    vn :: Var
    vn = if Set.null vs then 0 else Set.findMax vs + 1
      where
        vs = Set.fromList [x | p <- (c:ps), (_,xs) <- P.terms p, (x,_) <- P.mindices xs]

    coeffs :: [k]
    coeffs = head $ catMaybes $ [isLinearlyDependent cs2 | cs2 <- inits cs]
      where
        cmp = P.grlex
        ps' = GB.basis cmp ps
        cs  = iterate (\p -> P.reduce cmp (c * p) ps') 1

    isLinearlyDependent :: [Polynomial k Var] -> Maybe [k]
    isLinearlyDependent cs = if any (0/=) sol then Just sol else Nothing
      where
        cs2 = zip [vn..] cs
        sol = map (\(l,_) -> P.eval (\_ -> 1) $ P.reduce cmp2 (P.var l) gbase2) cs2
        cmp2   = P.grlex
        gbase2 = GB.basis cmp2 es
        es = Map.elems $ Map.fromListWith (+) $ do
          (n,xs) <- P.terms $ sum [P.var ln * cn | (ln,cn) <- cs2]
          let xs' = P.mindicesMap xs
              ys = P.mfromIndicesMap $ Map.filterWithKey (\x _ -> x <  vn) xs'
              zs = P.mfromIndicesMap $ Map.filterWithKey (\x _ -> x >= vn) xs'
          return (ys, P.fromTerm (n,zs))
