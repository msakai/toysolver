{-# LANGUAGE FlexibleInstances, DeriveDataTypeable, CPP #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Sign
-- Copyright   :  (c) Masahiro Sakai 2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (FlexibleInstances, DeriveDataTypeable, CPP)
--
-- Algebra of Signs.
--
-----------------------------------------------------------------------------
module Data.Sign
  (
  -- * Algebra of Sign
    Sign (..)
  , negate
  , abs
  , mult
  , recip
  , div
  , pow
  , signOf
  , symbol
  ) where

import qualified Prelude as P
import Prelude hiding (negate, abs, recip, div)
import Algebra.Enumerable (Enumerable (..), universeBounded) -- from lattices package
import qualified Algebra.Lattice as L -- from lattices package
import Control.DeepSeq
import Data.Hashable
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Typeable
import Data.Data
import qualified Numeric.Algebra as Alg

data Sign = Neg | Zero | Pos
  deriving (Eq, Ord, Show, Read, Enum, Bounded, Typeable, Data)

instance NFData Sign

instance Hashable Sign where hashWithSalt = hashUsing fromEnum

instance Enumerable Sign where
  universe = universeBounded

instance Alg.Multiplicative Sign where
  (*)   = mult
  pow1p s n = pow s (1+n)

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

abs :: Sign -> Sign
abs Neg  = Pos
abs Zero = Zero
abs Pos  = Pos

mult :: Sign -> Sign -> Sign
mult Pos s  = s
mult s Pos  = s
mult Neg s  = negate s
mult s Neg  = negate s
mult _ _    = Zero

recip :: Sign -> Sign
recip Pos  = Pos
recip Zero = error "Data.Sign.recip: division by Zero"
recip Neg  = Neg

div :: Sign -> Sign -> Sign
div s Pos  = s
div _ Zero = error "Data.Sign.div: division by Zero"
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

instance L.MeetSemiLattice (Set Sign) where
  meet = Set.intersection

instance L.Lattice (Set Sign)

instance L.BoundedMeetSemiLattice (Set Sign) where
  top = Set.fromList universe

instance L.BoundedLattice (Set Sign)

instance Num (Set Sign) where
  ss1 + ss2 = Set.unions [f s1 s2 | s1 <- Set.toList ss1, s2 <- Set.toList ss2]
    where
      f Zero s  = Set.singleton s
      f s Zero  = Set.singleton s
      f Pos Pos = Set.singleton Pos
      f Neg Neg = Set.singleton Neg
      f _ _     = Set.fromList [Neg,Zero,Pos]
  ss1 * ss2   = Set.fromList [mult s1 s2 | s1 <- Set.toList ss1, s2 <- Set.toList ss2]
  negate      = Set.map negate
  abs         = Set.map abs
  signum      = id
  fromInteger = Set.singleton . signOf

instance Fractional (Set Sign) where
  recip        = Set.map recip
  fromRational = Set.singleton . signOf

instance Alg.Multiplicative (Set Sign) where
  (*) = (*)
  pow1p s n = Alg.pow s (1+n)

instance Alg.Commutative (Set Sign)

instance Alg.Unital (Set Sign) where
  one = Set.singleton Pos
  pow = (Alg.^)

instance Alg.Division (Set Sign) where
  recip  = P.recip
  (/)    = (/)
  (\\)   = flip (/)
  ss ^ n = Set.map (\s -> pow s n) ss

instance Alg.Additive (Set Sign) where
  (+)           = (+)
  sinnum1p _ ss = ss

instance Alg.Abelian (Set Sign)

#if !MIN_VERSION_hashable(1,2,0)
-- Copied from hashable-1.2.0.7:
-- Copyright   :  (c) Milan Straka 2010
--                (c) Johan Tibell 2011
--                (c) Bryan O'Sullivan 2011, 2012

-- | Transform a value into a 'Hashable' value, then hash the
-- transformed value using the given salt.
--
-- This is a useful shorthand in cases where a type can easily be
-- mapped to another type that is already an instance of 'Hashable'.
-- Example:
--
-- > data Foo = Foo | Bar
-- >          deriving (Enum)
-- >
-- > instance Hashable Foo where
-- >     hashWithSalt = hashUsing fromEnum
hashUsing :: (Hashable b) =>
             (a -> b)           -- ^ Transformation function.
          -> Int                -- ^ Salt.
          -> a                  -- ^ Value to transform.
          -> Int
hashUsing f salt x = hashWithSalt salt (f x)
{-# INLINE hashUsing #-}
#endif

