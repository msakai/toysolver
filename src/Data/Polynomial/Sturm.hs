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
  ( SturmChain
  , sturmChain
  , numRoots
  , numRoots'
  , numRoots''
  , separate
  , separate'
  , narrow
  , narrow'
  , approx
  , approx'
  ) where

import Data.Maybe
import Data.Polynomial
import qualified Data.Interval as Interval
import Data.Interval (Interval)

type SturmChain = [UPolynomial Rational]

-- | Sturm's sequence 
sturmChain :: UPolynomial Rational -> SturmChain
sturmChain p = p0 : p1 : go p0 p1
  where
    x = ()
    p0 = p
    p1 = deriv p x
    go p q = if r==0 then [] else r : go q r
      where
        r = - (p `polyMod` q)

-- | the number of distinct real roots of p in (a,b]
numRoots
  :: UPolynomial Rational -- ^ p
  -> (Rational,Rational)  -- ^ (a,b)
  -> Int
numRoots p = numRoots' (sturmChain p)

-- | the number of distinct real roots of p in (a,b]
numRoots'
  :: SturmChain           -- ^ chain
  -> (Rational,Rational)  -- ^ (a,b)
  -> Int
numRoots' chain (a,b)
  | a < b     = n a - n b
  | otherwise = error $ "numRoots': \"" ++ show a ++ " < " ++ show b ++ "\" failed"
  where
    n x = countSignChanges [eval (\_ -> x) q | q <- chain]

-- | the number of distinct real roots of p in a given interval
numRoots''
  :: SturmChain
  -> Interval Rational
  -> Int
numRoots'' chain@(p:_) ival
  | Interval.null ival2 = 0
  | otherwise =
      case (Interval.lowerBound ival2, Interval.upperBound ival2) of
        (Just (in1,lb), Just (in2,ub)) ->
          (if lb==ub then 0 else (n lb - n ub)) +
          (if in1 && isRootOf lb p then 1 else 0) +
          (if not in2 && isRootOf ub p then -1 else 0)
        _ -> error "numRoots'': should not happen"
  where
    ival2 = boundInterval p ival
    n x = countSignChanges [eval (\() -> x) q | q <- chain]

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

boundInterval :: UPolynomial Rational -> Interval Rational -> Interval Rational
boundInterval p ival = Interval.intersection ival (Interval.closedInterval lb ub)
  where
    (lb,ub) = bounds p

-- disjoint intervals each of which contains exactly one real roots.
-- The intervals can be further narrowed by 'narrow'.
separate :: UPolynomial Rational -> [Interval Rational]
separate p = separate' (sturmChain p)

-- disjoint intervals each of which contains exactly one real roots.
-- The intervals can be further narrowed by 'narrow'.
separate' :: SturmChain -> [Interval Rational]
separate' chain@(p:_) = f (bounds p)
  where
    n x = countSignChanges [eval (\() -> x) q | q <- chain]

    f (lb,ub) =
      if lb `isRootOf` p
      then Interval.singleton lb : g (lb,ub)
      else g (lb,ub)
    
    g (lb,ub) =
      case n lb - n ub of
        0 -> []
        1 -> [Interval.interval (Just (False, lb)) (Just (True, ub))]
        _ -> g (lb, mid) ++ g (mid, ub)
      where
        mid = (lb + ub) / 2

narrow :: UPolynomial Rational -> Interval Rational -> Rational -> Interval Rational
narrow p ival size = narrow' (sturmChain p) ival size

narrow' :: SturmChain -> Interval Rational -> Rational -> Interval Rational
narrow' chain@(p:_) ival size = go (boundInterval p ival)
  where
    go ival
      | s < size = ival
      | numRoots'' chain ivalL > 0 = go ivalL
      | otherwise = go ivalR -- numRoots'' chain ivalR > 0
      where
        (_,lb) = fromJust $ Interval.lowerBound ival
        (_,ub) = fromJust $ Interval.upperBound ival
        s = ub - lb
        mid = (lb + ub) / 2
        ivalL = Interval.interval (Interval.lowerBound ival) (Just (True,mid))
        ivalR = Interval.interval (Just (False,mid)) (Interval.upperBound ival)

approx :: UPolynomial Rational -> Interval Rational -> Rational -> Rational
approx p = approx' (sturmChain p)

approx' :: SturmChain -> Interval Rational -> Rational -> Rational
approx' chain ival epsilon = fromJust $ Interval.pickup $ narrow' chain ival epsilon
