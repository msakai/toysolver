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
  , negate
  , mult
  , recip
  , div
  , pow
  , signOf
  , symbol
  ) where

import Prelude hiding (negate, recip, div)
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
  (*)   = mult
  pow1p = pow

instance Alg.Commutative Sign

instance Alg.Unital Sign where
  one = Pos
  pow = pow

instance Alg.Division Sign where
  recip = recip
  (/)   = div
  (\\)  = flip div
  (^)   = pow

negate :: Sign -> Sign
negate Neg  = Pos
negate Zero = Zero
negate Pos  = Neg

mult :: Sign -> Sign -> Sign
mult Pos s  = s
mult s Pos  = s
mult Neg s  = negate s
mult s Neg  = negate s
mult _ _    = Zero

recip :: Sign -> Sign
recip Pos  = Pos
recip Zero = error "signRecip: division by Zero"
recip Neg  = Neg

div :: Sign -> Sign -> Sign
div s Pos  = s
div _ Zero = error "signDiv: division by Zero"
div s Neg  = negate s

pow :: Integral x => Sign -> x -> Sign
pow _ 0    = Pos
pow Pos _  = Pos
pow Zero _ = Zero
pow Neg n  = if even n then Pos else Neg

signOf :: Real a => a -> Sign
signOf r =
  case r `compare` 0 of
    LT -> Neg
    EQ -> Zero
    GT -> Pos

symbol :: Sign -> String
symbol Pos  = "+"
symbol Neg  = "-"
symbol Zero = "0"


