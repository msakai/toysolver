{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
module Linear
  ( Linear (..)
  , (.-.)
  ) where

infixl 6 .+., .-.
infixl 7 .*.

class Linear k a | a -> k where
  (.*.) :: k -> a -> a
  (.+.) :: a -> a -> a

(.-.) :: (Num k, Linear k a) => a -> a -> a
a .-. b = a .+. (-1) .*. b
