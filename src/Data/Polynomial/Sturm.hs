-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Polynomial.Sturm
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
-- 
-- Reference:
-- 
-- * <http://en.wikipedia.org/wiki/Sturm%27s_theorem>
-- 
-- * <http://mathworld.wolfram.com/SturmFunction.html>
-- 
-----------------------------------------------------------------------------

module Data.Polynomial.Sturm
  ( numberOfDistinctRealRoots
  , sturmChain
  ) where

import Data.Polynomial

-- | the number of distinct real roots of p in (a,b]
numberOfDistinctRealRoots
  :: UPolynomial Rational -- ^ p
  -> (Rational,Rational)  -- ^ (a,b)
  -> Int
numberOfDistinctRealRoots p (a,b)
  | a < b     = n a - n b
  | otherwise = error $ "numberOfDistinctRealRoots: \"" ++ show a ++ " < " ++ show b ++ "\" failed"
  where
    chain = sturmChain p
    n x = countSignChanges [eval (\() -> x) q | q <- chain]

-- | Sturm's sequence 
sturmChain :: UPolynomial Rational -> [UPolynomial Rational]
sturmChain p = p0 : p1 : go p0 p1
  where
    x = ()
    p0 = p
    p1 = deriv p x
    go p q = if r==0 then [] else r : go q r
      where
        r = - (p `polyMod` q)

countSignChanges :: [Rational] -> Int
countSignChanges rs = countChanges xs
  where
    xs :: [Bool]
    xs = map (0<) . filter (0/=) $ rs

countChanges :: Eq a => [a] -> Int
countChanges [] = 0
countChanges (x:xs) = go x xs 0
  where
    go x [] r = r
    go x1 (x2:xs) r
      | x1==x2    = go x1 xs r
      | otherwise = go x2 xs (r+1)
