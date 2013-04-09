{-# LANGUAGE ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, DeriveDataTypeable #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Interval
-- Copyright   :  (c) Masahiro Sakai 2011-2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, DeriveDataTypeable)
--
-- Interval datatype and interval arithmetic.
--
-- Unlike the intervals package <http://hackage.haskell.org/package/intervals>,
-- this module provides both open and closed intervals and intended to be used
-- with @Rational@.
-- 
-----------------------------------------------------------------------------
module Data.Interval
  (
  -- * Interval type
    Interval
  , EndPoint (..)

  -- * Construction
  , interval
  , (<=..<=)
  , (<..<=)
  , (<=..<)
  , (<..<)
  , univ
  , empty
  , singleton

  -- * Query
  , null
  , member
  , notMember
  , isSubsetOf
  , isProperSubsetOf
  , lowerBound
  , upperBound
  , lowerBound'
  , upperBound'
  , size

  -- * Comparison
  , (<!), (<=!), (==!), (>=!), (>!)
  , (<?), (<=?), (==?), (>=?), (>?)

  -- * Combine
  , intersection
  , hull

  -- * Operations
  , pickup
  , tightenToInteger
  ) where

import Control.Exception (assert)
import Control.Monad hiding (join)
import Data.List hiding (null)
import Data.Maybe
import Data.Monoid
import Data.Lattice
import Data.Typeable
import Util (combineMaybe, isInteger)
import Prelude hiding (null)

-- | Interval
data Interval r = Interval !(EndPoint r, Bool) !(EndPoint r, Bool)
  deriving (Eq, Typeable)  

-- | Lower bound of the interval
lowerBound :: Num r => Interval r -> EndPoint r
lowerBound (Interval (lb,_) _) = lb

-- | Upper bound of the interval
upperBound :: Num r => Interval r -> EndPoint r
upperBound (Interval _ (ub,_)) = ub

-- | Lower bound of the interval and whether it is included in the interval
lowerBound' :: Num r => Interval r -> (EndPoint r, Bool)
lowerBound' (Interval lb _) = lb

-- | Upper bound of the interval and whether it is included in the interval
upperBound' :: Num r => Interval r -> (EndPoint r, Bool)
upperBound' (Interval _ ub) = ub

instance (Ord r, Num r) => Lattice (Interval r) where
  top    = univ
  bottom = empty
  join   = hull
  meet   = intersection

instance (Num r, Ord r, Show r) => Show (Interval r) where
  showsPrec p x | null x = showString "empty"
  showsPrec p x = showParen (p > appPrec) $
    showString "interval " .
    showsPrec appPrec1 (lowerBound x) .
    showChar ' ' . 
    showsPrec appPrec1 (upperBound x)

-- | smart constructor for 'Interval'
interval
  :: (Ord r, Num r)
  => (EndPoint r, Bool) -- ^ lower bound and whether it is included 
  -> (EndPoint r, Bool) -- ^ upper bound and whether it is included
  -> Interval r
interval lb@(x1,in1) ub@(x2,in2) =
  case x1 `compare` x2 of
    GT -> empty --  empty interval
    LT -> Interval (normalize lb) (normalize ub)
    EQ -> if in1 && in2 && isFinite x1 then Interval lb ub else empty
  where
    normalize x@(Finite _, _) = x
    normalize (x, _) = (x, False)

-- | closed interval [@l@,@u@]
(<=..<=)
  :: (Ord r, Num r)
  => EndPoint r -- ^ lower bound @l@
  -> EndPoint r -- ^ upper bound @u@
  -> Interval r
(<=..<=) lb ub = interval (lb, True) (ub, True)

-- | left-open right-closed interval (@l@,@u@]
(<..<=)
  :: (Ord r, Num r)
  => EndPoint r -- ^ lower bound @l@
  -> EndPoint r -- ^ upper bound @u@
  -> Interval r
(<..<=) lb ub = interval (lb, False) (ub, True)

-- | left-closed right-open interval [@l@, @u@)
(<=..<)
  :: (Ord r, Num r)
  => EndPoint r -- ^ lower bound @l@
  -> EndPoint r -- ^ upper bound @u@
  -> Interval r
(<=..<) lb ub = interval (lb, True) (ub, False)

-- | open interval (@l@, @u@)
(<..<)
  :: (Ord r, Num r)
  => EndPoint r -- ^ lower bound @l@
  -> EndPoint r -- ^ upper bound @u@
  -> Interval r
(<..<) lb ub = interval (lb, False) (ub, False)

-- | universal set (-∞, ∞)
univ :: (Num r, Ord r) => Interval r
univ = Interval (NegInf, False) (PosInf, False)

-- | empty (contradicting) interval
empty :: Num r => Interval r
empty = Interval (PosInf, False) (NegInf, False)

-- | singleton set \[x,x\]
singleton :: (Num r, Ord r) => r -> Interval r
singleton x = interval (Finite x, True) (Finite x, True)

-- | intersection (greatest lower bounds) of two intervals
intersection :: forall r. (Ord r, Num r) => Interval r -> Interval r -> Interval r
intersection (Interval l1 u1) (Interval l2 u2) = interval (maxLB l1 l2) (minUB u1 u2)
  where
    maxLB :: (EndPoint r, Bool) -> (EndPoint r, Bool) -> (EndPoint r, Bool)
    maxLB (x1,in1) (x2,in2) =
      ( max x1 x2
      , case x1 `compare` x2 of
          EQ -> in1 && in2
          LT -> in2
          GT -> in1
      )
    minUB :: (EndPoint r, Bool) -> (EndPoint r, Bool) -> (EndPoint r, Bool)
    minUB (x1,in1) (x2,in2) =
      ( min x1 x2
      , case x1 `compare` x2 of
          EQ -> in1 && in2
          LT -> in1
          GT -> in2
      )

-- | convex hull of two intervals
hull :: forall r. (Ord r, Num r) => Interval r -> Interval r -> Interval r
hull x1 x2
  | null x1 = x2
  | null x2 = x1
hull (Interval l1 u1) (Interval l2 u2) = interval (minLB l1 l2) (maxUB u1 u2)
  where
    maxUB :: (EndPoint r, Bool) -> (EndPoint r, Bool) -> (EndPoint r, Bool)
    maxUB (x1,in1) (x2,in2) =
      ( max x1 x2
      , case x1 `compare` x2 of
          EQ -> in1 || in2
          LT -> in2
          GT -> in1
      )
    minLB :: (EndPoint r, Bool) -> (EndPoint r, Bool) -> (EndPoint r, Bool)
    minLB (x1,in1) (x2,in2) =
      ( min x1 x2
      , case x1 `compare` x2 of
          EQ -> in1 || in2
          LT -> in1
          GT -> in2
      )

-- | Is the interval empty?
null :: Ord r => Interval r -> Bool
null (Interval (x1,in1) (x2,in2)) = 
  case x1 `compare` x2 of
    EQ -> assert (in1 && in2) False
    LT -> False
    GT -> True

-- | Is the element in the interval?
member :: Ord r => r -> Interval r -> Bool
member x (Interval (x1,in1) (x2,in2)) = condLB && condUB
  where
    condLB = if in1 then x1 <= Finite x else x1 < Finite x
    condUB = if in2 then Finite x <= x2 else Finite x < x2

-- | Is the element not in the interval?
notMember :: Ord r => r -> Interval r -> Bool
notMember a i = not $ member a i

-- | Is this a subset?
-- @(i1 `isSubsetOf` i2)@ tells whether @i1@ is a subset of @i2@.
isSubsetOf :: Ord r => Interval r -> Interval r -> Bool
isSubsetOf (Interval lb1 ub1) (Interval lb2 ub2) = testLB lb1 lb2 && testUB ub1 ub2
  where
    testLB (x1,in1) (x2,in2) =
      case x1 `compare` x2 of
        GT -> True
        LT -> False
        EQ -> not in1 || in2 -- in1 => in2
    testUB (x1,in1) (x2,in2) =
      case x1 `compare` x2 of
        LT -> True
        GT -> False
        EQ -> not in1 || in2 -- in1 => in2

-- | Is this a proper subset? (ie. a subset but not equal).
isProperSubsetOf :: Ord r => Interval r -> Interval r -> Bool
isProperSubsetOf i1 i2 = i1 /= i2 && i1 `isSubsetOf` i2

-- | Size of a interval. Size of an unbounded interval is @undefined@.
size :: (Num r, Ord r) => Interval r -> r
size x | null x = 0
size (Interval (Finite l, _) (Finite u, _)) = u - l
size _ = error "Data.Interval.size: unbounded interval"

-- | pick up an element from the interval if the interval is not empty.
pickup :: (Real r, Fractional r) => Interval r -> Maybe r
pickup (Interval (NegInf,in1) (PosInf,in2))   = Just 0
pickup (Interval (Finite x1, in1) (PosInf,_)) = Just $ if in1 then x1 else x1+1
pickup (Interval (NegInf,_) (Finite x2, in2)) = Just $ if in2 then x2 else x2-1
pickup (Interval (Finite x1, in1) (Finite x2, in2)) =
  case x1 `compare` x2 of
    GT -> Nothing
    LT -> Just $ (x1+x2) / 2
    EQ -> if in1 && in2 then Just x1 else Nothing
pickup x = Nothing

-- | tightening intervals by ceiling lower bounds and flooring upper bounds.
tightenToInteger :: forall r. (RealFrac r) => Interval r -> Interval r
tightenToInteger (Interval lb@(x1, in1) ub@(x2, in2)) = interval lb2 ub2
  where
    lb2 =
      case x1 of
        Finite x ->
          ( if isInteger x && not in1
            then Finite (x + 1)
            else Finite (fromInteger (ceiling x))
          , True
          )
        _ -> lb
    ub2 =
      case x2 of
        Finite x ->
          ( if isInteger x && not in2
            then Finite (x - 1)
            else Finite (fromInteger (floor x))
          , True
          )
        _ -> ub

-- | For all @x@ in @X@, @y@ in @Y@. @x '<' y@
(<!) :: Real r => Interval r -> Interval r -> Bool
a <! b =
  case ub_a `compare` lb_b of
    LT -> True
    GT -> False
    EQ ->
      case ub_a of
        NegInf   -> True -- a is empty, so it holds vacuously
        PosInf   -> True -- b is empty, so it holds vacuously
        Finite x -> not (in1 && in2)
  where
    (ub_a, in1) = upperBound' a
    (lb_b, in2) = lowerBound' b

-- | For all @x@ in @X@, @y@ in @Y@. @x '<=' y@
(<=!) :: Real r => Interval r -> Interval r -> Bool
a <=! b = upperBound a <= lowerBound b

-- | For all @x@ in @X@, @y@ in @Y@. @x '==' y@
(==!) :: Real r => Interval r -> Interval r -> Bool
a ==! b = a <=! b && a >=! b

-- | For all @x@ in @X@, @y@ in @Y@. @x '>=' y@
(>=!) :: Real r => Interval r -> Interval r -> Bool
(>=!) = flip (<=!)

-- | For all @x@ in @X@, @y@ in @Y@. @x '>' y@
(>!) :: Real r => Interval r -> Interval r -> Bool
(>!) = flip (<!)

-- | Does there exist an @x@ in @X@, @y@ in @Y@ such that @x '<' y@?
(<?) :: Real r => Interval r -> Interval r -> Bool
a <? b = lb_a < ub_b
  where
    lb_a = lowerBound a
    ub_b = upperBound b

-- | Does there exist an @x@ in @X@, @y@ in @Y@ such that @x '<=' y@?
(<=?) :: Real r => Interval r -> Interval r -> Bool
a <=? b　=
  case lb_a `compare` ub_b of
    LT -> True
    GT -> False
    EQ -> 
      case lb_a of
        NegInf -> False -- b is empty
        PosInf -> True  -- a is empty
        Finite x -> in1 && in2
  where
    (lb_a, in1) = lowerBound' a
    (ub_b, in2) = upperBound' b

-- | Does there exist an @x@ in @X@, @y@ in @Y@ such that @x '==' y@?
(==?) :: Real r => Interval r -> Interval r -> Bool
a ==? b = not $ null $ intersection a b

-- | Does there exist an @x@ in @X@, @y@ in @Y@ such that @x '>=' y@?
(>=?) :: Real r => Interval r -> Interval r -> Bool
(>=?) = flip (<=?)

-- | Does there exist an @x@ in @X@, @y@ in @Y@ such that @x '>' y@?
(>?) :: Real r => Interval r -> Interval r -> Bool
(>?) = flip (<?)

appPrec, appPrec1 :: Int
appPrec = 10
appPrec1 = appPrec + 1

scaleInterval :: Real r => r -> Interval r -> Interval r
scaleInterval _ x | null x = empty
scaleInterval c (Interval lb ub) =
  case compare c 0 of
    EQ -> singleton 0
    LT -> interval (scaleInf' c ub) (scaleInf' c lb)
    GT -> interval (scaleInf' c lb) (scaleInf' c ub)

instance forall r. (Real r, Fractional r) => Num (Interval r) where
  a + b | null a || null b = empty
  Interval lb1 ub1 + Interval lb2 ub2 = interval (f lb1 lb2) (g ub1 ub2)
    where
      f (Finite x1, in1) (Finite x2, in2) = (Finite (x1+x2), in1 && in2)
      f (NegInf,_) _ = (NegInf, False)
      f _ (NegInf,_) = (NegInf, False)
      f _ _ = error "Interval.(+) should not happen"

      g (Finite x1, in1) (Finite x2, in2) = (Finite (x1+x2), in1 && in2)
      g (PosInf,_) _ = (PosInf, False)
      g _ (PosInf,_) = (PosInf, False)
      g _ _ = error "Interval.(+) should not happen"

  negate a = scaleInterval (-1) a

  fromInteger i = singleton (fromInteger i)

  abs x = ((x `intersection` nonneg) `hull` (negate x `intersection` nonneg))
    where
      nonneg = Finite 0 <=..< PosInf

  signum x = zero `hull` pos `hull` neg
    where
      zero = if member 0 x then singleton 0 else empty
      pos = if null $ (Finite 0 <..< PosInf) `intersection` x
            then empty
            else singleton 1
      neg = if null $ (NegInf <..< Finite 0) `intersection` x
            then empty
            else singleton (-1)

  a * b | null a || null b = empty
  Interval lb1 ub1 * Interval lb2 ub2 = interval lb3 ub3
    where
      xs = [ mulInf' x1 x2 | x1 <- [lb1, ub1], x2 <- [lb2, ub2] ]
      ub3 = maximumBy cmpUB xs
      lb3 = minimumBy cmpLB xs

instance forall r. (Real r, Fractional r) => Fractional (Interval r) where
  fromRational r = singleton (fromRational r)
  recip a | null a = empty
  recip i | 0 `member` i = univ -- should be error?
  recip (Interval lb ub) = interval lb3 ub3
    where
      ub3 = maximumBy cmpUB xs
      lb3 = minimumBy cmpLB xs
      xs = [recipLB lb, recipUB ub]

cmpUB, cmpLB :: Real r => (EndPoint r, Bool) -> (EndPoint r, Bool) -> Ordering
cmpUB (x1,in1) (x2,in2) = compare x1 x2 `mappend` compare in1 in2
cmpLB (x1,in1) (x2,in2) = compare x1 x2 `mappend` flip compare in1 in2

-- | Endpoints of intervals
data EndPoint r
  = NegInf    -- ^ negative infinity
  | Finite !r -- ^ finite value
  | PosInf    -- ^ positive infinity
  deriving (Ord, Eq, Show, Typeable)

instance Bounded (EndPoint r) where
  minBound = NegInf
  maxBound = PosInf

isFinite :: EndPoint r -> Bool
isFinite (Finite _) = True
isFinite _ = False

negateEndPoint :: Num r => EndPoint r -> EndPoint r
negateEndPoint NegInf = PosInf
negateEndPoint PosInf = NegInf
negateEndPoint (Finite x) = Finite (negate x)

scaleInf' :: (Num r, Ord r) => r -> (EndPoint r, Bool) -> (EndPoint r, Bool)
scaleInf' a (x1, in1) = (scaleEndPoint a x1, in1)

scaleEndPoint :: (Num r, Ord r) => r -> EndPoint r -> EndPoint r
scaleEndPoint a inf =
  case a `compare` 0 of
    EQ -> Finite 0
    GT ->
      case inf of
        NegInf   -> NegInf
        Finite b -> Finite (a*b)
        PosInf   -> PosInf
    LT ->
      case inf of
        NegInf   -> PosInf
        Finite b -> Finite (a*b)
        PosInf   -> NegInf

mulInf' :: (Num r, Ord r) => (EndPoint r, Bool) -> (EndPoint r, Bool) -> (EndPoint r, Bool)
mulInf' (Finite 0, True) _ = (Finite 0, True)
mulInf' _ (Finite 0, True) = (Finite 0, True)
mulInf' (x1,in1) (x2,in2) = (mulEndPoint x1 x2, in1 && in2)

mulEndPoint :: (Num r, Ord r) => EndPoint r -> EndPoint r -> EndPoint r
mulEndPoint (Finite x1) (Finite x2) = Finite (x1 * x2)
mulEndPoint inf (Finite x2) =
  case compare x2 0 of
    EQ -> Finite 0
    GT -> inf
    LT -> negateEndPoint inf
mulEndPoint (Finite x1) inf =
  case compare x1 0 of
    EQ -> Finite 0
    GT -> inf
    LT -> negateEndPoint inf
mulEndPoint PosInf PosInf = PosInf
mulEndPoint PosInf NegInf = NegInf
mulEndPoint NegInf PosInf = NegInf
mulEndPoint NegInf NegInf = PosInf

recipLB :: (Fractional r, Ord r) => (EndPoint r, Bool) -> (EndPoint r, Bool)
recipLB (Finite 0, _) = (PosInf, False)
recipLB (x1, in1) = (recipEndPoint x1, in1)

recipUB :: (Fractional r, Ord r) => (EndPoint r, Bool) -> (EndPoint r, Bool)
recipUB (Finite 0, _) = (NegInf, False)
recipUB (x1, in1) = (recipEndPoint x1, in1)

recipEndPoint :: (Fractional r, Ord r) => EndPoint r -> EndPoint r
recipEndPoint PosInf = Finite 0
recipEndPoint NegInf = Finite 0
recipEndPoint (Finite x) = Finite (1/x)
