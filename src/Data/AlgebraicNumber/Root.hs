{-# LANGUAGE Rank2Types #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.AlgebraicNumber.Root
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (Rank2Types)
--
-- Manipulating polynomials for corresponding operations for algebraic numbers.
-- 
-- Reference:
--
-- * <http://www.dpmms.cam.ac.uk/~wtg10/galois.html>
-- 
-----------------------------------------------------------------------------
module Data.AlgebraicNumber.Root where

import Data.List
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Data.Polynomial (Polynomial, UPolynomial, X (..))
import qualified Data.Polynomial as P
import qualified Data.Polynomial.GroebnerBasis as GB

type Var = Int

{--------------------------------------------------------------------
  Manipulation of polynomials
--------------------------------------------------------------------}

normalizePoly :: UPolynomial Rational -> UPolynomial Rational
normalizePoly = P.toMonic P.umcmp

rootAdd :: UPolynomial Rational -> UPolynomial Rational -> UPolynomial Rational
rootAdd p1 p2 = lift2 (+) p1 p2

rootMul :: UPolynomial Rational -> UPolynomial Rational -> UPolynomial Rational
rootMul p1 p2 = lift2 (*) p1 p2

rootShift :: Rational -> UPolynomial Rational -> UPolynomial Rational
rootShift 0 p = p
rootShift r p = normalizePoly $ P.subst p (\X -> P.var X - P.constant r)

rootScale :: Rational -> UPolynomial Rational -> UPolynomial Rational
rootScale 0 p = P.var X
rootScale r p = normalizePoly $ P.subst p (\X -> P.constant (recip r) * P.var X)

rootRecip :: UPolynomial Rational -> UPolynomial Rational
rootRecip p = normalizePoly $ P.fromTerms [(c, P.var X `P.mpow` (d - P.deg xs)) | (c, xs) <- P.terms p]
  where
    d = P.deg p

-- 代数的数を係数とする多項式の根を、有理数係数多項式の根として表す
rootSimpPoly :: (a -> UPolynomial Rational) -> UPolynomial a -> UPolynomial Rational
rootSimpPoly f p = findPoly (P.var 0) ps
  where
    ys :: [(UPolynomial Rational, Var)]
    ys = zip (Set.toAscList $ Set.fromList [f c | (c, _) <- P.terms p]) [1..]

    m :: Map (UPolynomial Rational) Var
    m = Map.fromDistinctAscList ys

    p' :: Polynomial Rational Var
    p' = P.eval (\X -> P.var 0) (P.mapCoeff (\c -> P.var (m Map.! (f c))) p)

    ps :: [Polynomial Rational Var]
    ps = p' : [P.subst q (\X -> P.var x) | (q, x) <- ys]

rootNthRoot :: Integer -> UPolynomial Rational -> UPolynomial Rational
rootNthRoot n p = P.subst p (\X -> (P.var X)^n)

lift2 :: (forall a. Num a => a -> a -> a)
      -> UPolynomial Rational -> UPolynomial Rational -> UPolynomial Rational
lift2 f p1 p2 = findPoly f_a_b gbase
  where
    a, b :: Var
    a = 0
    b = 1

    f_a_b :: Polynomial Rational Var
    f_a_b = f (P.var a) (P.var b)

    gbase :: [Polynomial Rational Var]
    gbase = [ P.subst p1 (\X -> P.var a), P.subst p2 (\X -> P.var b) ]              

-- ps のもとで c を根とする多項式を求める
findPoly :: Polynomial Rational Var -> [Polynomial Rational Var] -> UPolynomial Rational
findPoly c ps = normalizePoly $ sum [P.constant coeff * (P.var X) ^ n | (n,coeff) <- zip [0..] coeffs]
  where  
    vn :: Var
    vn = if Set.null vs then 0 else Set.findMax vs + 1
      where
        vs = Set.fromList [x | p <- (c:ps), (_,xs) <- P.terms p, (x,_) <- P.mindices xs]

    coeffs :: [Rational]
    coeffs = head $ catMaybes $ [isLinearlyDependent cs2 | cs2 <- inits cs]
      where
        cmp = P.grlex
        ps' = GB.basis cmp ps
        cs  = iterate (\p -> P.reduce cmp (c * p) ps') 1

    isLinearlyDependent :: [Polynomial Rational Var] -> Maybe [Rational]
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
