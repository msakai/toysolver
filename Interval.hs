{-# LANGUAGE ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses #-}
module Interval
  ( EndPoint
  , Interval (..)
  , univR
  , singletonR
  , intersectR
  , pickupR
  ) where

import Linear
import Util (combineMaybe)

-- | Endpoint
-- (isInclusive, value)
type EndPoint r = Maybe (Bool, r)

data Interval r
  = Interval
  { lowerBound :: EndPoint r
  , upperBound :: EndPoint r
  }
  deriving (Eq,Ord,Show)

univR :: Interval r
univR = Interval Nothing Nothing

singletonR :: r -> Interval r
singletonR x = Interval (Just (True, x)) (Just (True, x))

intersectR :: forall r. RealFrac r => Interval r -> Interval r -> Interval r
intersectR (Interval l1 u1) (Interval l2 u2) = Interval (maxEP l1 l2) (minEP u1 u2)
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

pickupR :: RealFrac r => Interval r -> Maybe r
pickupR (Interval Nothing Nothing) = Just 0
pickupR (Interval (Just (in1,x1)) Nothing) = Just $ if in1 then x1 else x1+1
pickupR (Interval Nothing (Just (in2,x2))) = Just $ if in2 then x2 else x2-1
pickupR (Interval (Just (in1,x1)) (Just (in2,x2))) =
  case x1 `compare` x2 of
    GT -> Nothing
    LT -> Just $ (x1+x2) / 2
    EQ -> if in1 && in2 then Just x1 else Nothing

-- Interval airthmetics.
-- Note that this instance does not satisfy algebraic laws of linear spaces.
instance (RealFrac r) => Linear r (Interval r) where
  zero = singletonR 0
  Interval lb1 ub1 .+. Interval lb2 ub2 = Interval (f lb1 lb2) (f ub1 ub2)
    where
      f = combineMaybe $ \(in1,x1) (in2,x2) -> (in1 && in2, x1 + x2)
  c .*. Interval lb ub
    | c < 0     = Interval (f ub) (f lb)
    | otherwise = Interval (f lb) (f ub)
    where
      f Nothing = Nothing
      f (Just (incl,val)) = Just (incl, c * val)
