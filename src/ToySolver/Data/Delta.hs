{-# LANGUAGE TypeFamilies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.Delta
-- Copyright   :  (c) Masahiro Sakai 2011-2013
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- Augmenting number types with infinitesimal parameter δ.
--
-- Reference:
--
-- * Bruno Dutertre and Leonardo de Moura,
--   \"/A Fast Linear-Arithmetic Solver for DPLL(T)/\",
--   Computer Aided Verification In Computer Aided Verification, Vol. 4144
--   (2006), pp. 81-94.
--   <https://doi.org/10.1007/11817963_11>
--   <http://yices.csl.sri.com/cav06.pdf>
--
-----------------------------------------------------------------------------

module ToySolver.Data.Delta
  (
  -- * The Delta type
    Delta (..)

  -- * Construction
  , fromReal
  , delta

  -- * Query
  , realPart
  , deltaPart

  -- * Relationship with integers
  , floor'
  , ceiling'
  , isInteger'
  ) where

import Data.VectorSpace
import ToySolver.Internal.Util (isInteger)

-- | @Delta r k@ represents r + kδ for symbolic infinitesimal parameter δ.
data Delta r = Delta !r !r deriving (Ord, Eq, Show)

-- | symbolic infinitesimal parameter δ.
delta :: Num r => Delta r
delta = Delta 0 1

-- | Conversion from a base @r@ value to @Delta r@.
fromReal :: Num r => r -> Delta r
fromReal x = Delta x 0

-- | Extracts the real part..
realPart :: Delta r -> r
realPart (Delta r _) = r

-- | Extracts the δ part..
deltaPart :: Delta r -> r
deltaPart (Delta _ k) = k

instance Num r => AdditiveGroup (Delta r) where
  Delta r1 k1 ^+^ Delta r2 k2 = Delta (r1+r2) (k1+k2)
  zeroV = Delta 0 0
  negateV (Delta r k) = Delta (- r) (- k)

instance Num r => VectorSpace (Delta r) where
  type Scalar (Delta r) = r
  c *^ Delta r k = Delta (c*r) (c*k)

-- | This instance assumes the symbolic infinitesimal parameter δ is a nilpotent with δ² = 0.
instance (Num r, Ord r) => Num (Delta r) where
  (+) = (^+^)
  negate = negateV
  Delta r1 k1 * Delta r2 k2 = Delta (r1*r2) (r1*k2+r2*k1)
  abs x =
    case x `compare` 0 of
      LT -> negateV x
      EQ -> x
      GT -> x
  signum x =
    case x `compare` 0 of
      LT -> -1
      EQ -> 0
      GT -> 1
  fromInteger x = Delta (fromInteger x) 0

-- | This is unsafe instance in the sense that only a proper real can be a divisor.
instance (Fractional r, Ord r) => Fractional (Delta r) where
  Delta r1 k1 / Delta r2 0  = Delta (r1 / r2) (k1 / r2)
  Delta r1 k1 / Delta r2 k2 =
    error "Fractional{ToySolver.Data.Delta.Delta}.(/): divisor must be a proper real"
  fromRational x = Delta (fromRational x) 0

instance (Real r, Eq r) => Real (Delta r) where
  toRational (Delta r 0) = toRational r
  toRational (Delta r k) =
    error "Real{ToySolver.Data.Delta.Delta}.toRational: not a real number"

instance (RealFrac r, Eq r) => RealFrac (Delta r) where
  properFraction x =
    case x `compare` 0 of
      LT -> let n = ceiling' x in (n, x - fromIntegral n)
      EQ -> (0, 0)
      GT -> let n = floor' x in (n, x - fromIntegral n)
  ceiling = ceiling'
  floor   = floor'

-- | 'Delta' version of 'floor'.
-- @'floor'' x@ returns the greatest integer not greater than @x@
floor' :: (RealFrac r, Integral a) => Delta r -> a
floor' (Delta r k) = fromInteger $ if r2==r && k < 0 then i-1 else i
  where
    i = floor r
    r2 = fromInteger i

-- | 'Delta' version of 'ceiling'.
-- @'ceiling'' x@ returns the least integer not less than @x@
ceiling' :: (RealFrac r, Integral a) => Delta r -> a
ceiling' (Delta r k) = fromInteger $ if r2==r && k > 0 then i+1 else i
  where
    i = ceiling r
    r2 = fromInteger i

-- | Is this a integer?
isInteger' :: RealFrac r => Delta r -> Bool
isInteger' (Delta r k) = isInteger r && k == 0
