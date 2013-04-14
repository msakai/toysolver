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
-- Algebraic nubmers (work in progress).
--
-- Reference:
--
-- * <http://www.dpmms.cam.ac.uk/~wtg10/galois.html>
-- 
-----------------------------------------------------------------------------
module Data.AlgebraicNumber.Root where

import Data.List
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

import Data.Polynomial
import Data.Polynomial.GBase

type Var = Int

{--------------------------------------------------------------------
  Manipulation of polynomials
--------------------------------------------------------------------}

rootAdd :: UPolynomial Rational -> UPolynomial Rational -> UPolynomial Rational
rootAdd p1 p2 = lift2 (+) p1 p2

rootSub :: UPolynomial Rational -> UPolynomial Rational -> UPolynomial Rational
rootSub p1 p2 = lift2 (flip subtract) p1 p2

rootMul :: UPolynomial Rational -> UPolynomial Rational -> UPolynomial Rational
rootMul p1 p2 = lift2 (*) p1 p2

rootNegate :: UPolynomial Rational -> UPolynomial Rational
rootNegate p = fromTerms [(if (d - mmDegree xs) `mod` 2 == 0 then c else -c, xs) | (c, xs) <- terms p]
  where
    d = deg p

rootScale :: Rational -> UPolynomial Rational -> UPolynomial Rational
rootScale r p = fromTerms [(r^(d - mmDegree xs) * c, xs) | (c, xs) <- terms p]
  where
    d = deg p

rootRecip :: UPolynomial Rational -> UPolynomial Rational
rootRecip p = fromTerms [(c, mmFromList [(X, d - mmDegree xs)]) | (c, xs) <- terms p]
  where
    d = deg p

-- 代数的数を係数とする多項式の根を、有理数係数多項式の根として表す
rootSimpPoly :: (a -> UPolynomial Rational) -> UPolynomial a -> UPolynomial Rational
rootSimpPoly f p = findPoly (var 0) ps
  where
    ys :: [(UPolynomial Rational, Var)]
    ys = zip (Set.toAscList $ Set.fromList [f c | (c, _) <- terms p]) [1..]

    m :: Map.Map (UPolynomial Rational) Var
    m = Map.fromDistinctAscList ys

    p' :: Polynomial Rational Var
    p' = eval (\X -> var 0) (mapCoeff (\c -> var (m Map.! (f c))) p)

    ps :: [Polynomial Rational Var]
    ps = p' : [mapVar (\X -> x) q | (q, x) <- ys]

lift2 :: (forall a. Num a => a -> a -> a)
      -> UPolynomial Rational -> UPolynomial Rational -> UPolynomial Rational
lift2 f p1 p2 = findPoly f_a_b gbase
  where
    a, b :: Var
    a = 0
    b = 1

    f_a_b :: Polynomial Rational Var
    f_a_b = f (var a) (var b)

    gbase :: [Polynomial Rational Var]
    gbase = [ mapVar (\X -> a) p1, mapVar (\X -> b) p2 ]              

-- ps のもとで c を根とする多項式を求める
findPoly :: Polynomial Rational Var -> [Polynomial Rational Var] -> UPolynomial Rational
findPoly c ps = fromTerms [(coeff, mmFromList [(X, n)]) | (n,coeff) <- zip [0..] coeffs]
  where  
    vn :: Var
    vn = if Set.null vs then 0 else Set.findMax vs + 1
      where
        vs = Set.fromList [x | p <- (c:ps), (_,xs) <- terms p, (x,_) <- mmToList xs]

    coeffs :: [Rational]
    coeffs = head $ catMaybes $ [isLinearlyDependent cs2 | cs2 <- inits cs]
      where
        cmp = grlex
        ps' = buchberger cmp ps
        cs  = iterate (\p -> reduce cmp (c * p) ps') 1

    isLinearlyDependent :: [Polynomial Rational Var] -> Maybe [Rational]
    isLinearlyDependent cs = if any (0/=) sol then Just sol else Nothing
      where
        cs2 = zip [vn..] cs
        sol = map (\(l,_) -> eval (\_ -> 1) $ reduce cmp2 (var l) gbase2) cs2
        cmp2   = grlex
        gbase2 = buchberger cmp2 es
        es = Map.elems $ Map.fromListWith (+) $ do
          (n,xs) <- terms $ sum [var ln * cn | (ln,cn) <- cs2]
          let xs' = mmToList xs
              ys = mmFromList [(x,m) | (x,m) <- xs', x < vn]
              zs = mmFromList [(x,m) | (x,m) <- xs', x >= vn]
          return (ys, fromMonomial (n,zs))
