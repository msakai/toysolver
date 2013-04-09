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
-- * \"/Sturm's theorem/.\" Wikipedia, The Free Encyclopedia. Wikimedia Foundation, Inc.
--   2012-06-23. <http://en.wikipedia.org/wiki/Sturm%27s_theorem>
-- 
-- * Weisstein, Eric W. \"/Sturm Function/.\" From MathWorld--A Wolfram Web Resource.
--   <http://mathworld.wolfram.com/SturmFunction.html>
-- 
-----------------------------------------------------------------------------

module Data.Polynomial.Sturm
  ( SturmChain
  , sturmChain
  , numRoots
  , numRoots'
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
import Data.Interval (Interval, EndPoint (..), (<..<=), (<=..<=))

-- | Sturm's chain (Sturm's sequence)
type SturmChain = [UPolynomial Rational]

-- | Sturm's sequence of a polynomial
sturmChain :: UPolynomial Rational -> SturmChain
sturmChain p = p0 : p1 : go p0 p1
  where
    x = ()
    p0 = p
    p1 = deriv p x
    go p q = if r==0 then [] else r : go q r
      where
        r = - (p `polyMod` q)

-- | The number of distinct real roots of @p@ in a given interval
numRoots
  :: UPolynomial Rational
  -> Interval Rational
  -> Int
numRoots p ival = numRoots' (sturmChain p) ival

-- | The number of distinct real roots of @p@ in a given interval.
-- This function takes @p@'s sturm chain instead of @p@ itself.
numRoots'
  :: SturmChain
  -> Interval Rational
  -> Int
numRoots' chain@(p:_) ival
  | Interval.null ival2 = 0
  | otherwise =
      case (Interval.lowerBound ival2, Interval.upperBound ival2) of
        (Finite lb, Finite ub) ->
          (if lb==ub then 0 else (n lb - n ub)) +
          (if lb `Interval.member` ival2 && isRootOf lb p then 1 else 0) +
          (if ub `Interval.notMember` ival2 && isRootOf ub p then -1 else 0)
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
boundInterval p ival = Interval.intersection ival (Finite lb <=..<= Finite ub)
  where
    (lb,ub) = bounds p

-- | Disjoint intervals each of which contains exactly one real roots of the given polynoimal @p@.
-- The intervals can be further narrowed by 'narrow' or 'narrow''.
separate :: UPolynomial Rational -> [Interval Rational]
separate p = separate' (sturmChain p)

-- | Disjoint intervals each of which contains exactly one real roots of the given polynoimal @p@.
-- The intervals can be further narrowed by 'narrow' or 'narrow''.
-- This function takes @p@'s sturm chain instead of @p@ itself.
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
        1 -> [Finite lb <..<= Finite ub]
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
      | numRoots' chain ivalL > 0 = go ivalL
      | otherwise = go ivalR -- numRoots' chain ivalR > 0
      where
        Finite lb = Interval.lowerBound ival
        Finite ub = Interval.upperBound ival
        s = ub - lb
        mid = (lb + ub) / 2
        ivalL = Interval.interval (Interval.lowerBound' ival) (Finite mid, True)
        ivalR = Interval.interval (Finite mid, False) (Interval.upperBound' ival)

approx :: UPolynomial Rational -> Interval Rational -> Rational -> Rational
approx p = approx' (sturmChain p)

approx' :: SturmChain -> Interval Rational -> Rational -> Rational
approx' chain ival epsilon = fromJust $ Interval.pickup $ narrow' chain ival epsilon
