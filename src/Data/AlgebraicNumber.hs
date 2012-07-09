{-# LANGUAGE Rank2Types #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.AlgebraicNumber
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
module Data.AlgebraicNumber
  (
  -- * Algebraic real type
    AReal

  -- * Construction
  , realRoots

  -- * Properties
  , minimalPolynomial
  , deg
  , isAlgebraicInteger

  -- * Real-like functions
  , toRational'

  -- * RealFrac-like functions
  , properFraction'
  , truncate'
  , round'
  , ceiling'
  , floor'

  -- * Misc
  , simpARealPoly  
  ) where

import Control.Exception (assert)
import Control.Monad
import Data.List
import Data.Ratio

import Data.Polynomial hiding (deg)
import qualified Data.Polynomial as P
import qualified Data.Polynomial.Sturm as Sturm
import qualified Data.Polynomial.FactorZ as FactorZ
import Data.Interval (Interval, (<!), (>!))
import qualified Data.Interval as Interval
import Data.AlgebraicNumber.Root

{--------------------------------------------------------------------
  Algebraic numbers

以下の代数的実数の場合にはスツルムの定理による根の分離で色々できているけど、
一般の代数的数の場合にどうすれば良いかはまだちゃんと理解できていない。
なので、一旦色々削除した。
--------------------------------------------------------------------}

{--------------------------------------------------------------------
  Algebraic reals
--------------------------------------------------------------------}

data AReal = RealRoot (UPolynomial Integer) (Interval Rational)
  deriving Show

-- | Real roots of the rational coefficient polynomial.
realRoots :: UPolynomial Rational -> [AReal]
realRoots p = sort $ do
  q <- FactorZ.factor $ toZ p
  guard $ P.deg q > 0
  let d = foldl1' gcd [c | (c,_) <- terms q]
      q' = if q==0
           then q
           else mapCoeff (`div` d) q
  i <- Sturm.separate (mapCoeff fromInteger q')
  return $ RealRoot q' i

minimalPolynomial :: AReal -> UPolynomial Rational
minimalPolynomial (RealRoot p _) = mapCoeff f p
  where
    (c,_) = leadingTerm grlex p
    f x = x % c

isZero :: AReal -> Bool
isZero (RealRoot p i) = 0 `Interval.member` i && 0 `isRootOf` p

instance Eq AReal where
  a == b = (compare a b == EQ)

instance Ord AReal where
  compare a@(RealRoot _ i1) b@(RealRoot _ i2)
    | i1 >! i2 = GT
    | i1 <! i2 = LT
    | isZero c = EQ
    | Sturm.numRoots p' ipos == 1 = GT
    | otherwise = assert (Sturm.numRoots p' ineg == 1) LT
    where
      c@(RealRoot p i3) = a - b
      p' = mapCoeff fromInteger p
      ipos = Interval.intersection i3 (Interval.interval (Just (False,0)) Nothing)
      ineg = Interval.intersection i3 (Interval.interval Nothing (Just (False,0)))

instance Num AReal where
  RealRoot p1 i1 + RealRoot p2 i2 = RealRoot p3 i3
    where
      p3 = rootAdd p1 p2
      i3 = go i1 i2 (Sturm.separate p3')

      p1' = mapCoeff fromInteger p1
      p2' = mapCoeff fromInteger p2
      p3' = mapCoeff fromInteger p3

      go i1 i2 is3 =
        case [i5 | i3 <- is3, let i5 = Interval.intersection i3 i4, Sturm.numRoots p3' i5 > 0] of
          [] -> error "AReal.+: should not happen"
          [i5] -> i5
          is5 ->
            go (Sturm.narrow p1' i1 (Interval.size i1 / 2))
               (Sturm.narrow p2' i2 (Interval.size i2 / 2))
               [Sturm.narrow p3' i5 (Interval.size i5 / 2) | i5 <- is5]
        where
          i4 = i1 + i2

  RealRoot p1 i1 * RealRoot p2 i2 = RealRoot p3 i3
    where
      p3 = rootMul p1 p2
      i3 = go i1 i2 (Sturm.separate p3')

      p1' = mapCoeff fromInteger p1
      p2' = mapCoeff fromInteger p2
      p3' = mapCoeff fromInteger p3

      go i1 i2 is3 =
        case [i5 | i3 <- is3, let i5 = Interval.intersection i3 i4, Sturm.numRoots p3' i5 > 0] of
          [] -> error "AReal.*: should not happen"
          [i5] -> i5
          is5 ->
            go (Sturm.narrow p1' i1 (Interval.size i1 / 2))
               (Sturm.narrow p2' i2 (Interval.size i2 / 2))
               [Sturm.narrow p3' i5 (Interval.size i5 / 2) | i5 <- is5]
        where
          i4 = i1 * i2

  negate (RealRoot p i) = RealRoot (rootNegate p) (-i)

  abs a =
    case compare 0 a of
      EQ -> fromInteger 0
      LT -> a
      GT -> negate a

  signum a = fromInteger $
    case compare 0 a of
      EQ -> 0
      LT -> 1
      GT -> -1

  fromInteger i = RealRoot (x - constant i) (Interval.singleton (fromInteger i))
    where
      x = var ()

instance Fractional AReal where
  fromRational r = RealRoot (toZ (x - constant r)) (Interval.singleton r)
    where
      x = var ()

  recip a@(RealRoot p i)
    | isZero a  = error "AReal.recip: zero division"
    | otherwise = RealRoot (rootRecip p) (recip i)

toRational' :: AReal -> Rational -> Rational
toRational' (RealRoot p i) epsilon = Sturm.approx (mapCoeff toRational p) i epsilon

-- | Same as 'properFraction'.
properFraction' :: Integral b => AReal -> (b, AReal)
properFraction' x =
  case compare x 0 of
    EQ -> (0, 0)
    GT -> (fromInteger floor_x, x - fromInteger floor_x)
    LT -> (fromInteger ceiling_x, x - fromInteger ceiling_x)
  where
    floor_x   = floor' x
    ceiling_x = ceiling' x

-- | Same as 'truncate'.
truncate' :: Integral b => AReal -> b
truncate' = fst . properFraction'

-- | Same as 'round'.
round' :: Integral b => AReal -> b
round' x = 
  case signum (abs r - 0.5) of
    -1 -> n
    0  -> if even n then n else m
    1  -> m
    _  -> error "round default defn: Bad value"
  where
    (n,r) = properFraction' x
    m = if r < 0 then n - 1 else n + 1

-- | Same as 'ceiling'.
ceiling' :: Integral b => AReal -> b
ceiling' (RealRoot p i) =
  if Sturm.numRoots' chain (Interval.intersection i2 i3) > 1
    then fromInteger ceiling_lb
    else fromInteger ceiling_ub
  where
    chain = Sturm.sturmChain (mapCoeff fromInteger p)
    i2 = Sturm.narrow' chain i (1/2)
    Just (inLB, lb) = Interval.lowerBound i2
    Just (inUB, ub) = Interval.upperBound i2
    ceiling_lb = ceiling lb
    ceiling_ub = ceiling ub
    i3 = Interval.interval Nothing (Just (True, fromInteger ceiling_lb))

-- | Same as 'floor'.
floor' :: Integral b => AReal -> b
floor' (RealRoot p i) =
  if Sturm.numRoots' chain (Interval.intersection i2 i3) > 1
    then fromInteger floor_ub
    else fromInteger floor_lb
  where
    chain = Sturm.sturmChain (mapCoeff fromInteger p)
    i2 = Sturm.narrow' chain i (1/2)
    Just (inLB, lb) = Interval.lowerBound i2
    Just (inUB, ub) = Interval.upperBound i2
    floor_lb = floor lb
    floor_ub = floor ub
    i3 = Interval.interval (Just (True, fromInteger floor_ub)) Nothing

{--------------------------------------------------------------------
  Properties
--------------------------------------------------------------------}

deg :: AReal -> Integer
deg (RealRoot p _) = P.deg p

isAlgebraicInteger :: AReal -> Bool
isAlgebraicInteger (RealRoot p _) = c==1
  where
    (c,_) = leadingTerm grlex p

{--------------------------------------------------------------------
  Manipulation of polynomials
--------------------------------------------------------------------}

-- 代数的数を係数とする多項式の根を、有理数係数多項式の根として表す
simpARealPoly :: UPolynomial AReal -> UPolynomial Integer
simpARealPoly p = rootSimpPoly (\(RealRoot q _) -> q) p
