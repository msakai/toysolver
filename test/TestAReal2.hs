{-# LANGUAGE TemplateHaskell #-}

import Data.Maybe
import Data.Ratio
import Test.HUnit hiding (Test)
import Test.QuickCheck
import Test.Framework (Test, defaultMain, testGroup)
import Test.Framework.TH
import Test.Framework.Providers.HUnit
import Test.Framework.Providers.QuickCheck2

import Data.Polynomial (UPolynomial, X (..))
import qualified Data.Polynomial as P
import Data.AlgebraicNumber.Real

import Control.Monad
import System.IO

{--------------------------------------------------------------------
  Num
--------------------------------------------------------------------}

prop_add_comm =
  forAll areals $ \a ->
  forAll areals $ \b ->
    a + b == b + a

prop_add_assoc =
  forAll areals $ \a ->
  forAll areals $ \b ->
  forAll areals $ \c ->
    a + (b + c) == (a + b) + c

prop_add_unitL =
  forAll areals $ \a ->
    0 + a == a

prop_add_unitR =
  forAll areals $ \a ->
    a + 0 == a

prop_mult_comm =
  forAll areals $ \a ->
  forAll areals $ \b ->
    a * b == b * a

prop_mult_assoc =
  forAll areals $ \a ->
  forAll areals $ \b ->
  forAll areals $ \c ->
    a * (b * c) == (a * b) * c

prop_mult_unitL =
  forAll areals $ \a ->
    1 * a == a

prop_mult_unitR =
  forAll areals $ \a ->
    a * 1 == a

prop_mult_dist =
  forAll areals $ \a ->
  forAll areals $ \b ->
  forAll areals $ \c ->
    a * (b + c) == a * b + a * c

prop_mult_zero = 
  forAll areals $ \a ->
    0 * a ==  0

{--------------------------------------------------------------------
  Generators
--------------------------------------------------------------------}

areals :: Gen AReal
areals = oneof $ map return $ samples

samples :: [AReal]
samples = [0, 1, -1, 2, -2] ++ concatMap realRoots ps
  where
    x = P.var X
    ps = [x^2 - 2, x^2 - 3 {- , x^3 - 2, x^6 + 6*x^3 - 2*x^2 + 9 -}]

------------------------------------------------------------------------
-- Test harness

main :: IO ()
main = $(defaultMainGenerator)
