module IntervalR
  ( EndPoint
  , IntervalR (..)
  , univR
  , intersectR
  , pickupR
  ) where

import Util (combineMaybe)

-- | Endpoint
-- (isInclusive, value)
type EndPoint = Maybe (Bool, Rational)

data IntervalR
  = IntervalR
  { lowerBound :: EndPoint
  , upperBound :: EndPoint
  }
  deriving (Eq,Ord,Show)

univR :: IntervalR
univR = IntervalR Nothing Nothing

intersectR :: IntervalR -> IntervalR -> IntervalR
intersectR (IntervalR l1 u1) (IntervalR l2 u2) = IntervalR (maxEP l1 l2) (minEP u1 u2)
  where 
    maxEP :: EndPoint -> EndPoint -> EndPoint
    maxEP = combineMaybe $ \(in1,x1) (in2,x2) ->
      ( case x1 `compare` x2 of
          EQ -> in1 && in2
          LT -> in2
          GT -> in1
      , max x1 x2
      )

    minEP :: EndPoint -> EndPoint -> EndPoint
    minEP = combineMaybe $ \(in1,x1) (in2,x2) ->
      ( case x1 `compare` x2 of
          EQ -> in1 && in2
          LT -> in1
          GT -> in2
      , min x1 x2
      )

pickupR :: IntervalR -> Maybe Rational
pickupR (IntervalR Nothing Nothing) = Just 0
pickupR (IntervalR (Just (in1,x1)) Nothing) = Just $ if in1 then x1 else x1+1
pickupR (IntervalR Nothing (Just (in2,x2))) = Just $ if in2 then x2 else x2-1
pickupR (IntervalR (Just (in1,x1)) (Just (in2,x2))) =
  case x1 `compare` x2 of
    GT -> Nothing
    LT -> Just $ (x1+x2) / 2
    EQ -> if in1 && in2 then Just x1 else Nothing
