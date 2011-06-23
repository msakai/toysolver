module IntervalR
  ( EP
  , IntervalR
  , univR
  , intersectR
  , pickupR
  ) where

import Util (combineMaybe)

-- | Endpoint
-- (isInclusive, value)
type EP = Maybe (Bool, Rational)

type IntervalR = (EP, EP)

univR :: IntervalR
univR = (Nothing, Nothing)

intersectR :: IntervalR -> IntervalR -> IntervalR
intersectR (l1,u1) (l2,u2) = (maxEP l1 l2, minEP u1 u2)
  where 
    maxEP :: EP -> EP -> EP
    maxEP = combineMaybe $ \(in1,x1) (in2,x2) ->
      ( case x1 `compare` x2 of
          EQ -> in1 && in2
          LT -> in2
          GT -> in1
      , max x1 x2
      )

    minEP :: EP -> EP -> EP
    minEP = combineMaybe $ \(in1,x1) (in2,x2) ->
      ( case x1 `compare` x2 of
          EQ -> in1 && in2
          LT -> in1
          GT -> in2
      , min x1 x2
      )

pickupR :: IntervalR -> Maybe Rational
pickupR (Nothing,Nothing) = Just 0
pickupR (Just (in1,x1), Nothing) = Just $ if in1 then x1 else x1+1
pickupR (Nothing, Just (in2,x2)) = Just $ if in2 then x2 else x2-1
pickupR (Just (in1,x1), Just (in2,x2)) =
  case x1 `compare` x2 of
    GT -> Nothing
    LT -> Just $ (x1+x2) / 2
    EQ -> if in1 && in2 then Just x1 else Nothing
