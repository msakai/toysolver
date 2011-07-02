module Util where

combineMaybe :: (a -> a -> a) -> Maybe a -> Maybe a -> Maybe a
combineMaybe _ Nothing y = y
combineMaybe _ x Nothing = x
combineMaybe f (Just x) (Just y) = Just (f x y)

isInteger :: RealFrac a => a -> Bool
isInteger x = fromInteger (round x) == x

fracPart :: RealFrac a => a -> a
fracPart x = x - fromInteger (floor x)
