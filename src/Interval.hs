{-# LANGUAGE ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Interval
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses)
--
-- Interval datatype.
-- 
-----------------------------------------------------------------------------
module Interval
  ( EndPoint
  , Interval
  , lowerBound
  , upperBound
  , interval
  , univ
  , empty
  , singleton
  , intersection
  , pickup
  ) where

import Control.Monad
import Linear
import Util (combineMaybe)

-- | Endpoint
-- (isInclusive, value)
type EndPoint r = Maybe (Bool, r)

-- | interval
data Interval r
  = Interval
  { lowerBound :: EndPoint r -- ^ lower bound of the interval
  , upperBound :: EndPoint r -- ^ upper bound of the interval
  }
  deriving (Eq,Ord,Show)

-- | smart constructor for 'Interval'
interval :: Real r => EndPoint r -> EndPoint r -> Interval r
interval lb@(Just (in1,x1)) ub@(Just (in2,x2)) =
  case x1 `compare` x2 of
    GT -> empty
    LT -> Interval lb ub
    EQ -> if in1 && in2 then Interval lb ub else empty
interval lb ub = Interval lb ub

-- | (-∞, ∞)
univ :: Interval r
univ = Interval Nothing Nothing

-- | empty (contradicting) interval
empty :: Num r => Interval r
empty = Interval (Just (False,0)) (Just (False,0))

-- | singleton set \[x,x\]
singleton :: r -> Interval r
singleton x = Interval (Just (True, x)) (Just (True, x))

-- | intersection of two intervals
intersection :: forall r. Real r => Interval r -> Interval r -> Interval r
intersection (Interval l1 u1) (Interval l2 u2) = interval (maxEP l1 l2) (minEP u1 u2)
  where 
    maxEP :: EndPoint r -> EndPoint r -> EndPoint r
    maxEP = combineMaybe $ \(in1,x1) (in2,x2) ->
      ( case x1 `compare` x2 of
          EQ -> in1 && in2
          LT -> in2
          GT -> in1
      , max x1 x2
      )

    minEP :: EndPoint r -> EndPoint r -> EndPoint r
    minEP = combineMaybe $ \(in1,x1) (in2,x2) ->
      ( case x1 `compare` x2 of
          EQ -> in1 && in2
          LT -> in1
          GT -> in2
      , min x1 x2
      )

-- | pick up an element from the interval if the interval is not empty.
pickup :: (Real r, Fractional r) => Interval r -> Maybe r
pickup (Interval Nothing Nothing) = Just 0
pickup (Interval (Just (in1,x1)) Nothing) = Just $ if in1 then x1 else x1+1
pickup (Interval Nothing (Just (in2,x2))) = Just $ if in2 then x2 else x2-1
pickup (Interval (Just (in1,x1)) (Just (in2,x2))) =
  case x1 `compare` x2 of
    GT -> Nothing
    LT -> Just $ (x1+x2) / 2
    EQ -> if in1 && in2 then Just x1 else Nothing

-- | Interval airthmetics.
-- Note that this instance does not satisfy algebraic laws of linear spaces.
instance (Real r) => Linear r (Interval r) where
  lzero = singleton 0
  Interval lb1 ub1 .+. Interval lb2 ub2 = interval (f lb1 lb2) (f ub1 ub2)
    where
      f = liftM2 $ \(in1,x1) (in2,x2) -> (in1 && in2, x1 + x2)
  c .*. Interval lb ub
    | c < 0     = interval (f ub) (f lb)
    | otherwise = interval (f lb) (f ub)
    where
      f Nothing = Nothing
      f (Just (incl,val)) = Just (incl, c * val)
