{-# LANGUAGE TypeFamilies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Delta
-- Copyright   :  (c) Masahiro Sakai 2011-2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (TypeFamilies)
--
-- Augmenting number types with infinitesimal parameter δ.
--
-- Reference:
-- 
-- * Bruno Dutertre and Leonardo de Moura,
--   \"/A Fast Linear-Arithmetic Solver for DPLL(T)/\",
--   Computer Aided Verification In Computer Aided Verification, Vol. 4144
--   (2006), pp. 81-94.
--   <http://dx.doi.org/10.1007/11817963_11>
--   <http://yices.csl.sri.com/cav06.pdf>
--
-----------------------------------------------------------------------------

module Data.Delta
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
