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
  , separate
  ) where

import Data.Polynomial
import qualified Data.Interval as Interval

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

-- | Closed interval that contains all real roots of a given polynomial.
-- 根の限界
-- <http://aozoragakuen.sakura.ne.jp/taiwa/taiwaNch02/node26.html>
bounds :: UPolynomial Rational -> (Rational, Rational)
bounds p = (-m, m)
  where
    m = if p==0
        then 0
        else max 1 (sum [abs (c/s) | (c,_) <- terms p] - 1)
    (s,_) = leadingTerm grlex p

-- disjoint intervals each of which contains exactly one real roots.
separate :: UPolynomial Rational -> [Interval.Interval Rational]
separate p = f (bounds p)
  where
    chain = sturmChain p
    n x = countSignChanges [eval (\() -> x) q | q <- chain]

    f (lb,ub) =
      if eval (\() -> lb) p == 0
      then Interval.singleton lb : g (lb,ub)
      else g (lb,ub)
    
    g (lb,ub) =
      case n lb - n ub of
        0 -> []
        1 -> [Interval.interval (Just (False, lb)) (Just (True, ub))]
        _ -> g (lb, mid) ++ g (mid, ub)
      where
        mid = (lb + ub) / 2
