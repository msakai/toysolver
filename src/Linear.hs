{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
module Linear
  ( Linear (..)
  ) where

import Data.Ratio

infixl 6 .+., .-.
infixl 7 .*.

class Num k => Linear k a | a -> k where
  (.*.) :: k -> a -> a
  (.+.) :: a -> a -> a
  lzero :: a

  lnegate :: a -> a
  lnegate x = (-1) .*. x

  (.-.) :: a -> a -> a
  a .-. b = a .+. lnegate b

  lsum :: [a] -> a
  lsum = foldr (.+.) lzero

instance Integral a => Linear (Ratio a) (Ratio a) where
  (.*.) = (*)
  (.+.) = (+)
  lzero = 0

instance Linear Integer Integer where
  (.*.) = (*)
  (.+.) = (+)
  lzero = 0

instance Linear Double Double where
  (.*.) = (*)
  (.+.) = (+)
  lzero = 0
