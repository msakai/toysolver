{-# LANGUAGE DeriveDataTypeable #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Sign
-- Copyright   :  (c) Masahiro Sakai 2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (DeriveDataTypeable)
--
-- Algebra of Signs.
--
-----------------------------------------------------------------------------
module Data.Sign
  (
  -- * Algebra of Sign
    Sign (..)
  , signNegate
  , signMul
  , signRecip
  , signDiv
  , signPow
  , signOf
  , showSign
  ) where

import Algebra.Enumerable (Enumerable (..)) -- from lattices package
import Control.DeepSeq
import Data.Typeable
import Data.Data
import qualified Numeric.Algebra as Alg

data Sign = Neg | Zero | Pos
  deriving (Eq, Ord, Show, Read, Enum, Bounded, Typeable, Data)

instance NFData Sign

instance Enumerable Sign where
  universe = [Neg .. Pos]

instance Alg.Multiplicative Sign where
  (*)   = signMul
  pow1p = signPow

instance Alg.Commutative Sign

instance Alg.Unital Sign where
  one = Pos
  pow = signPow

instance Alg.Division Sign where
  recip = signRecip
  (/)   = signDiv
  (\\)  = flip signDiv
  (^)   = signPow

signNegate :: Sign -> Sign
signNegate Neg  = Pos
signNegate Zero = Zero
signNegate Pos  = Neg

signMul :: Sign -> Sign -> Sign
signMul Pos s  = s
signMul s Pos  = s
signMul Neg s  = signNegate s
signMul s Neg  = signNegate s
signMul _ _    = Zero

signRecip :: Sign -> Sign
signRecip Pos  = Pos
signRecip Zero = error "signRecip: division by Zero"
signRecip Neg  = Neg

signDiv :: Sign -> Sign -> Sign
signDiv s Pos  = s
signDiv _ Zero = error "signDiv: division by Zero"
signDiv s Neg  = signNegate s

signPow :: Integral x => Sign -> x -> Sign
signPow _ 0    = Pos
signPow Pos _  = Pos
signPow Zero _ = Zero
signPow Neg n  = if even n then Pos else Neg

signOf :: Real a => a -> Sign
signOf r =
  case r `compare` 0 of
    LT -> Neg
    EQ -> Zero
    GT -> Pos

showSign :: Sign -> String
showSign Pos  = "+"
showSign Neg  = "-"
showSign Zero = "0"

