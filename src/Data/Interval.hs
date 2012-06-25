{-# LANGUAGE ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, DeriveDataTypeable #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Interval
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, DeriveDataTypeable)
--
-- Interval datatype.
-- 
-----------------------------------------------------------------------------
module Data.Interval
  (
  -- * Interval type
    Interval
  , EndPoint

  -- * Construction
  , interval
  , closedInterval
  , openInterval
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
  , size

  -- * Combine
  , intersection
  , join

  -- * Operations
  , pickup
  , tightenToInteger
  ) where

import Control.Monad hiding (join)
import Data.List hiding (null)
import Data.Maybe
import Data.Monoid
import Data.Linear
import Data.Lattice
import Data.Typeable
import Util (combineMaybe, isInteger)
import Prelude hiding (null)

-- | Interval
data Interval r
  = Empty
  | Interval (EndPoint r) (EndPoint r)
  deriving (Eq, Typeable)  

-- | Lower bound of the interval
lowerBound :: Num r => Interval r -> EndPoint r
lowerBound Empty = Just (False,0)
lowerBound (Interval lb _) = lb

-- | Upper bound of the interval
upperBound :: Num r => Interval r -> EndPoint r
upperBound Empty = Just (False,0)
upperBound (Interval _ ub) = ub

-- | Endpoint
-- 
-- > (isInclusive, value)
type EndPoint r = Maybe (Bool, r)

instance (Ord r, Num r) => Lattice (Interval r) where
  top    = univ
  bottom = empty
  join   = join'
  meet   = intersection

instance (Num r, Show r) => Show (Interval r) where
  showsPrec p x  = showParen (p > appPrec) $
    showString "interval " .
    showsPrec appPrec1 (lowerBound x) .
    showChar ' ' . 
    showsPrec appPrec1 (upperBound x)

-- | smart constructor for 'Interval'
interval
  :: (Ord r, Num r)
  => EndPoint r -- ^ lower bound
  -> EndPoint r -- ^ upper bound
  -> Interval r
interval lb@(Just (in1,x1)) ub@(Just (in2,x2)) =
  case x1 `compare` x2 of
    GT -> empty
    LT -> Interval lb ub
    EQ -> if in1 && in2 then Interval lb ub else empty
interval lb ub = Interval lb ub

-- | closed set [@l, @u]
closedInterval
  :: (Ord r, Num r)
  => r -- ^ lower bound @l@
  -> r -- ^ upper bound @u@
  -> Interval r
closedInterval lb ub = interval (Just (True, lb)) (Just (True, ub))

-- | open set (@l, @u)
openInterval
  :: (Ord r, Num r)
  => r -- ^ lower bound @l@
  -> r -- ^ upper bound @u@
  -> Interval r
openInterval lb ub = interval (Just (False, lb)) (Just (False, ub))

-- | universal set (-∞, ∞)
univ :: (Num r, Ord r) => Interval r
univ = interval Nothing Nothing

-- | empty (contradicting) interval
empty :: Num r => Interval r
empty = Empty

-- | singleton set \[x,x\]
singleton :: (Num r, Ord r) => r -> Interval r
singleton x = interval (Just (True, x)) (Just (True, x))

-- | intersection (greatest lower bounds) of two intervals
intersection :: forall r. (Ord r, Num r) => Interval r -> Interval r -> Interval r
intersection (Interval l1 u1) (Interval l2 u2) = interval (maxLB l1 l2) (minUB u1 u2)
  where
    maxLB :: EndPoint r -> EndPoint r -> EndPoint r
    maxLB = combineMaybe $ \(in1,x1) (in2,x2) ->
      ( case x1 `compare` x2 of
          EQ -> in1 && in2
          LT -> in2
          GT -> in1
      , max x1 x2
      )
    minUB :: EndPoint r -> EndPoint r -> EndPoint r
    minUB = combineMaybe $ \(in1,x1) (in2,x2) ->
      ( case x1 `compare` x2 of
          EQ -> in1 && in2
          LT -> in1
          GT -> in2
      , min x1 x2
      )
intersection _ _ = empty

-- | join (least upperbound) of two intervals.
join' :: forall r. (Ord r, Num r) => Interval r -> Interval r -> Interval r
join' Empty x2 = x2
join' x1 Empty = x1
join' (Interval l1 u1) (Interval l2 u2) = interval (minLB l1 l2) (maxUB u1 u2)
  where
    maxUB :: EndPoint r -> EndPoint r -> EndPoint r
    maxUB u1 u2 = do
      (in1,x1) <- u1
      (in2,x2) <- u2
      return $
        ( case x1 `compare` x2 of
          EQ -> in1 || in2
          LT -> in2
          GT -> in1
        , max x1 x2
        )
    minLB :: EndPoint r -> EndPoint r -> EndPoint r
    minLB l1 l2 = do
      (in1,x1) <- l1
      (in2,x2) <- l2
      return $
        ( case x1 `compare` x2 of
          EQ -> in1 || in2
          LT -> in1
          GT -> in2
        , min x1 x2
        )

-- | Is the interval empty?
null :: Ord r => Interval r -> Bool
null Empty = True
null _ = False

-- | Is the element in the interval?
member :: Ord r => r -> Interval r -> Bool
member _ Empty = False
member x (Interval lb ub) = testLB x lb && testUB x ub
  where
    testLB x Nothing = True
    testLB x (Just (in1,x1)) = if in1 then x1 <= x else x1 < x
    testUB x Nothing = True
    testUB x (Just (in2,x2)) = if in2 then x <= x2 else x < x2

-- | Is the element not in the interval?
notMember :: Ord r => r -> Interval r -> Bool
notMember a i = not $ member a i

-- | Is this a subset?
-- @(i1 `isSubsetOf` i2)@ tells whether @i1@ is a subset of @i2@.
isSubsetOf :: Ord r => Interval r -> Interval r -> Bool
isSubsetOf Empty _ = True
isSubsetOf _ Empty = False
isSubsetOf (Interval lb1 ub1) (Interval lb2 ub2) = testLB lb1 lb2 && testUB ub1 ub2
  where
    testLB _ Nothing = True
    testLB (Just (in1,x1)) (Just (in2,x2)) =
      case x1 `compare` x2 of
        GT -> True
        LT -> False
        EQ -> not in1 || in2 -- in1 => in2
    testLB Nothing _ = False

    testUB _ Nothing = True
    testUB (Just (in1,x1)) (Just (in2,x2)) =
      case x1 `compare` x2 of
        LT -> True
        GT -> False
        EQ -> not in1 || in2 -- in1 => in2
    testUB Nothing _ = False

-- | Is this a proper subset? (ie. a subset but not equal).
isProperSubsetOf :: Ord r => Interval r -> Interval r -> Bool
isProperSubsetOf i1 i2 = i1 /= i2 && i1 `isSubsetOf` i2

-- | Size of a interval. Size of an unbounded interval is @undefined@.
size :: (Num r, Ord r) => Interval r -> r
size Empty = 0
size (Interval (Just (_,l)) (Just (_,u))) = u - l
size _ = error "Data.Interval.size: unbounded interval"

-- | pick up an element from the interval if the interval is not empty.
pickup :: (Real r, Fractional r) => Interval r -> Maybe r
pickup Empty = Nothing
pickup (Interval Nothing Nothing) = Just 0
pickup (Interval (Just (in1,x1)) Nothing) = Just $ if in1 then x1 else x1+1
pickup (Interval Nothing (Just (in2,x2))) = Just $ if in2 then x2 else x2-1
pickup (Interval (Just (in1,x1)) (Just (in2,x2))) =
  case x1 `compare` x2 of
    GT -> Nothing
    LT -> Just $ (x1+x2) / 2
    EQ -> if in1 && in2 then Just x1 else Nothing

-- | tightening intervals by ceiling lower bounds and flooring upper bounds.
tightenToInteger :: forall r. (RealFrac r) => Interval r -> Interval r
tightenToInteger Empty = Empty
tightenToInteger (Interval lb ub) = interval (fmap tightenLB lb) (fmap tightenUB ub)
  where
    tightenLB (incl,lb) =
      ( True
      , if isInteger lb && not incl
        then lb + 1
        else fromIntegral (ceiling lb :: Integer)
      )
    tightenUB (incl,ub) =
      ( True
      , if isInteger ub && not incl
        then ub - 1
        else fromIntegral (floor ub :: Integer)
      )

-- | Interval airthmetics.
-- Note that this instance does not satisfy algebraic laws of linear spaces.
instance Real r => Module r (Interval r) where
  lzero = singleton 0

  Interval lb1 ub1 .+. Interval lb2 ub2 = interval (f lb1 lb2) (f ub1 ub2)
    where
      f = liftM2 $ \(in1,x1) (in2,x2) -> (in1 && in2, x1 + x2)
  _ .+. _ = Empty

  _ .*. Empty = Empty
  c .*. Interval lb ub =
    case compare c 0 of
      EQ -> singleton 0
      LT -> interval (f ub) (f lb)
      GT -> interval (f lb) (f ub)
    where
      f Nothing = Nothing
      f (Just (incl,val)) = Just (incl, c * val)

instance (Real r, Fractional r) => Linear r (Interval r)

appPrec, appPrec1 :: Int
appPrec = 10
appPrec1 = appPrec + 1


instance forall r. (Real r, Fractional r) => Num (Interval r) where
  a + b = a .+. b
  a - b = a .-. b
  negate a = (-1) .*. a
  fromInteger i = singleton (fromInteger i)

  abs x = ((x `intersection` nonneg) `join` (negate x `intersection` nonneg))
    where
      nonneg = interval (Just (True,0)) Nothing

  signum x = zero `join` pos `join` neg
    where
      zero = if member 0 x then singleton 0 else empty
      pos = if null $ intersection (interval (Just (False,0)) Nothing) x
            then empty
            else singleton 1
      neg = if null $ intersection (interval Nothing (Just (False,0))) x
            then empty
            else singleton (-1)

  Interval lb1 ub1 * Interval lb2 ub2 = interval lb3 ub3
    where
      xs = [ mulInf' x1 x2
           | x1 <- [lbToInf lb1, ubToInf ub1]
           , x2 <- [lbToInf lb2, ubToInf ub2]
           ]
      ub3 = infToUB $ maximumBy cmpUB xs
      lb3 = infToLB $ minimumBy cmpLB xs
  _ * _ = Empty

instance forall r. (Real r, Fractional r) => Fractional (Interval r) where
  fromRational r = singleton (fromRational r)
  recip Empty = Empty
  recip i | 0 `member` i = univ -- should be error?
  recip (Interval lb ub) = interval lb3 ub3
    where
      ub3 = infToUB $ maximumBy cmpUB xs
      lb3 = infToLB $ minimumBy cmpLB xs
      xs = [recipLB (lbToInf lb), recipUB (ubToInf ub)]

data Inf r = NegInf | Finite !r | PosInf
  deriving (Ord, Eq)

cmpUB, cmpLB :: Real r => (Bool, Inf r) -> (Bool, Inf r) -> Ordering
cmpUB (in1,x1) (in2,x2) = compare x1 x2 `mappend` compare in1 in2
cmpLB (in1,x1) (in2,x2) = compare x1 x2 `mappend` flip compare in1 in2

negateInf :: Num r => Inf r -> Inf r
negateInf NegInf = PosInf
negateInf PosInf = NegInf
negateInf (Finite x) = Finite (negate x)

mulInf' :: (Num r, Ord r) => (Bool, Inf r) -> (Bool, Inf r) -> (Bool, Inf r)
mulInf' (True, Finite 0) _ = (True, Finite 0)
mulInf' _ (True, Finite 0) = (True, Finite 0)
mulInf' (in1,x1) (in2,x2) = (in1 && in2, mulInf x1 x2)

mulInf :: (Num r, Ord r) => Inf r -> Inf r -> Inf r
mulInf (Finite x1) (Finite x2) = Finite (x1 * x2)
mulInf inf (Finite x2) =
  case compare x2 0 of
    EQ -> Finite 0
    GT -> inf
    LT -> negateInf inf
mulInf (Finite x1) inf =
  case compare x1 0 of
    EQ -> Finite 0
    GT -> inf
    LT -> negateInf inf
mulInf PosInf PosInf = PosInf
mulInf PosInf NegInf = NegInf
mulInf NegInf PosInf = NegInf
mulInf NegInf NegInf = PosInf

recipLB :: (Fractional r, Ord r) => (Bool, Inf r) -> (Bool, Inf r)
recipLB (_, Finite 0) = (False, PosInf)
recipLB (in1, x1) = (in1, recipInf x1)

recipUB :: (Fractional r, Ord r) => (Bool, Inf r) -> (Bool, Inf r)
recipUB (_, Finite 0) = (False, NegInf)
recipUB (in1, x1) = (in1, recipInf x1)

recipInf :: (Fractional r, Ord r) => Inf r -> Inf r
recipInf PosInf = Finite 0
recipInf NegInf = Finite 0
recipInf (Finite x) = Finite (1/x)

lbToInf :: Num r => EndPoint r -> (Bool, Inf r)
lbToInf Nothing = (False, NegInf)
lbToInf (Just (in1,x1)) = (in1, Finite x1)

ubToInf :: Num r => EndPoint r -> (Bool, Inf r)
ubToInf Nothing = (False, PosInf)
ubToInf (Just (in1,x1)) = (in1, Finite x1)

infToLB :: Num r => (Bool, Inf r) -> EndPoint r
infToLB (in1, Finite x)  = Just (in1, x)
infToLB (False, NegInf)  = Nothing
infToLB (_, PosInf)      = error "infToLB: should not happen"
infToLB (True, NegInf)   = error "infToLB: should not happen"

infToUB :: Num r => (Bool, Inf r) -> EndPoint r
infToUB (in1, Finite x)  = Just (in1, x)
infToUB (False, PosInf)  = Nothing
infToUB (_, NegInf)      = error "infToUB: should not happen"
infToUB (True, PosInf)   = error "infToUB: should not happen"
