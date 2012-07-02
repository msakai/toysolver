{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}

import Data.Maybe
import Data.Ratio
import Test.HUnit hiding (Test)
import Test.QuickCheck
import Test.Framework (Test, defaultMain, testGroup)
import Test.Framework.TH
import Test.Framework.Providers.HUnit
import Test.Framework.Providers.QuickCheck2

import Data.Polynomial
import Data.AlgebraicNumber
import Data.AlgebraicNumber.Root

import Control.Monad
import System.IO

{--------------------------------------------------------------------
  sample values
--------------------------------------------------------------------}

-- ±√2
sqrt2 :: AReal
[neg_sqrt2, sqrt2] = realRoots (x^2 - 2)
  where
    x = var ()

-- ±√3
sqrt3 :: AReal
[neg_sqrt3, sqrt3] = realRoots (x^2 - 3)
  where
    x = var ()

{--------------------------------------------------------------------
  root manipulation
--------------------------------------------------------------------}

case__rootAdd_sqrt2_sqrt3 = assertBool "" $ abs valP <= 0.0001
  where
    x = var ()

    p :: UPolynomial Integer
    p = rootAdd (x^2 - 2) (x^2 - 3)

    valP :: Double
    valP = eval (\() -> sqrt 2 + sqrt 3) $ mapCoeff fromInteger p

-- bug?
test_rootAdd = p
  where
    x = var ()    
    p :: UPolynomial Integer
    p = rootAdd (x^2 - 2) (x^6 + 6*x^3 - 2*x^2 + 9)

case_rootSub_sqrt2_sqrt3 = assertBool "" $ abs valP <= 0.0001
  where
    x = var ()

    p :: UPolynomial Integer
    p = rootSub (x^2 - 2) (x^2 - 3)

    valP :: Double
    valP = eval (\() -> sqrt 2 - sqrt 3) $ mapCoeff fromInteger p

case_rootMul_sqrt2_sqrt3 = assertBool "" $ abs valP <= 0.0001
  where
    x = var ()

    p :: UPolynomial Integer
    p = rootMul (x^2 - 2) (x^2 - 3)

    valP :: Double
    valP = eval (\() -> sqrt 2 * sqrt 3) $ mapCoeff fromInteger p

case_rootNegate_test1 = assertBool "" $ abs valP <= 0.0001
  where
    x = var ()

    p :: UPolynomial Integer
    p = rootNegate (x^3 - 3)

    valP :: Double
    valP = eval (\() -> - (3 ** (1/3))) $ mapCoeff fromInteger p

case_rootNegate_test2 = rootNegate p @?= q
  where
    x :: UPolynomial Integer
    x = var ()
    p = x^3 - 3
    q = x^3 + 3

case_rootNegate_test3 = rootNegate p @?= q
  where
    x :: UPolynomial Integer
    x = var ()
    p = (x-2)*(x-3)*(x-4)
    q = (x+2)*(x+3)*(x+4)

case_rootScale = rootScale 2 p @?= q
  where
    x :: UPolynomial Integer
    x = var ()
    p = (x-2)*(x-3)*(x-4)
    q = (x-4)*(x-6)*(x-8)

case_rootRecip = assertBool "" $ abs valP <= 0.0001
  where
    x = var ()

    p :: UPolynomial Integer
    p = rootRecip (x^3 - 3)

    valP :: Double
    valP = eval (\() -> 1 / (3 ** (1/3))) $ mapCoeff fromInteger p

{--------------------------------------------------------------------
  algebraic reals
--------------------------------------------------------------------}

case_realRoot_minus_one = realRoots (x^2 + 1) @?= []
  where
    x = var ()

case_realRoot_two = length (realRoots (x^2 - 2)) @?= 2
  where
    x = var ()

case_eq = sqrt2*sqrt2 - 2 @?= 0

case_eq_refl = assertBool "" $ sqrt2 == sqrt2

case_diseq_1 = assertBool "" $ sqrt2 /= sqrt3

case_diseq_2 = assertBool "" $ sqrt2 /= neg_sqrt2

case_cmp_1 = assertBool "" $ 0 < sqrt2

case_cmp_2 = assertBool "" $ neg_sqrt2 < 0

case_cmp_3 = assertBool "" $ 0 < neg_sqrt2 * neg_sqrt2

case_cmp_4 = assertBool "" $ neg_sqrt2 * neg_sqrt2 * neg_sqrt2 < 0

case_floor_sqrt2 = floor' sqrt2 @?= 1

case_floor_neg_sqrt2 = floor' neg_sqrt2 @?= -2

case_floor_1 = floor' 1 @?= 1

case_floor_neg_1 = floor' (-1) @?= -1

case_ceiling_sqrt2 = ceiling' sqrt2 @?= 2

case_ceiling_neg_sqrt2 = ceiling' neg_sqrt2 @?= -1

case_ceiling_1 = ceiling' 1 @?= 1

case_ceiling_neg_1 = ceiling' (-1) @?= -1

case_round_sqrt2 = round' sqrt2 @?= 1

-- 期待値は Wolfram Alpha で x^3 - Sqrt[2]*x + 3 を調べて Real root の exact form で得た
case_simpARealPoly = simpARealPoly p @?= q
  where
    x :: forall k. (Num k, Eq k) => UPolynomial k
    x = var ()
    p = x^3 - constant sqrt2 * x + 3
    q = x^6 + 6*x^3 - 2*x^2 + 9

------------------------------------------------------------------------
-- Test harness

main :: IO ()
main = $(defaultMainGenerator)
