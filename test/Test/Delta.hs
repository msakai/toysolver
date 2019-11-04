{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
module Test.Delta (deltaTestGroup) where

import Data.VectorSpace ((*^))
import Test.Tasty
import Test.Tasty.QuickCheck hiding ((.&&.), (.||.))
import Test.Tasty.TH
import ToySolver.Data.Delta (Delta (..))
import qualified ToySolver.Data.Delta as Delta

-- ---------------------------------------------------------------------
-- Delta

instance Arbitrary r => Arbitrary (Delta r) where
  arbitrary = do
    r <- arbitrary
    k <- arbitrary
    return (Delta r k)

prop_Delta_add_comm :: Property
prop_Delta_add_comm =
  forAll arbitrary $ \(a :: Delta Rational) ->
  forAll arbitrary $ \b ->
    a + b == b + a

prop_Delta_add_assoc :: Property
prop_Delta_add_assoc =
  forAll arbitrary $ \(a :: Delta Rational) ->
  forAll arbitrary $ \b ->
  forAll arbitrary $ \c ->
    a + (b + c) == (a + b) + c

prop_Delta_add_unitL :: Property
prop_Delta_add_unitL =
  forAll arbitrary $ \(a :: Delta Rational) ->
    0 + a == a

prop_Delta_add_unitR :: Property
prop_Delta_add_unitR =
  forAll arbitrary $ \(a :: Delta Rational) ->
    a + 0 == a

prop_Delta_mult_comm :: Property
prop_Delta_mult_comm =
  forAll arbitrary $ \(a :: Delta Rational) ->
  forAll arbitrary $ \b ->
    a * b == b * a

prop_Delta_mult_assoc :: Property
prop_Delta_mult_assoc =
  forAll arbitrary $ \(a :: Delta Rational) ->
  forAll arbitrary $ \b ->
  forAll arbitrary $ \c ->
    a * (b * c) == (a * b) * c

prop_Delta_mult_unitL :: Property
prop_Delta_mult_unitL =
  forAll arbitrary $ \(a :: Delta Rational) ->
    1 * a == a

prop_Delta_mult_unitR :: Property
prop_Delta_mult_unitR =
  forAll arbitrary $ \(a :: Delta Rational) ->
    a * 1 == a

prop_Delta_mult_dist :: Property
prop_Delta_mult_dist =
  forAll arbitrary $ \(a :: Delta Rational) ->
  forAll arbitrary $ \b ->
  forAll arbitrary $ \c ->
    a * (b + c) == a * b + a * c

prop_Delta_mult_zero :: Property
prop_Delta_mult_zero =
  forAll arbitrary $ \(a :: Delta Rational) ->
    0 * a ==  0

prop_Delta_scale_mult :: Property
prop_Delta_scale_mult =
  forAll arbitrary $ \(a :: Delta Rational) ->
  forAll arbitrary $ \b ->
    Delta.fromReal a * b ==  a *^ b

prop_Delta_signum_abs :: Property
prop_Delta_signum_abs =
  forAll arbitrary $ \(x :: Delta Rational) ->
    abs x * signum x == x

prop_Delta_floor :: Property
prop_Delta_floor =
  forAll arbitrary $ \(x :: Delta Rational) ->
    let y :: Integer
        y = Delta.floor' x
    in fromIntegral y <= x && x < fromIntegral (y+1)

prop_Delta_ceiling :: Property
prop_Delta_ceiling =
  forAll arbitrary $ \(x :: Delta Rational) ->
    let y :: Integer
        y = Delta.ceiling' x
    in fromIntegral (y-1) < x && x <= fromIntegral y

prop_Delta_properFraction :: Property
prop_Delta_properFraction =
  forAll arbitrary $ \(x :: Delta Rational) ->
    let n :: Integer
        (n,f) = properFraction x
    in and
       [ abs f < 1
       , not (x >= 0) || (n >= 0 && f >= 0)
       , not (x <= 0) || (n <= 0 && f <= 0)
       ]

------------------------------------------------------------------------
-- Test harness

deltaTestGroup :: TestTree
deltaTestGroup = $(testGroupGenerator)
