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
import Data.AlgebraicNumber.Real
import Data.AlgebraicNumber.Root
import qualified Data.Interval as Interval

import Control.Monad
import Control.Exception
import System.IO

{--------------------------------------------------------------------
  sample values
--------------------------------------------------------------------}

-- ±√2
sqrt2 :: AReal
[neg_sqrt2, sqrt2] = realRoots (x^2 - 2)
  where
    x = var X

-- ±√3
sqrt3 :: AReal
[neg_sqrt3, sqrt3] = realRoots (x^2 - 3)
  where
    x = var X

{--------------------------------------------------------------------
  root manipulation
--------------------------------------------------------------------}

case_rootAdd_sqrt2_sqrt3 = assertBool "" $ abs valP <= 0.0001
  where
    x = var X

    p :: UPolynomial Rational
    p = rootAdd (x^2 - 2) (x^2 - 3)

    valP :: Double
    valP = eval (\X -> sqrt 2 + sqrt 3) $ mapCoeff fromRational p

-- bug?
sample_rootAdd = p
  where
    x = var X    
    p :: UPolynomial Rational
    p = rootAdd (x^2 - 2) (x^6 + 6*x^3 - 2*x^2 + 9)

case_rootSub_sqrt2_sqrt3 = assertBool "" $ abs valP <= 0.0001
  where
    x = var X

    p :: UPolynomial Rational
    p = rootAdd (x^2 - 2) (rootScale (-1) (x^2 - 3))

    valP :: Double
    valP = eval (\X -> sqrt 2 - sqrt 3) $ mapCoeff fromRational p

case_rootMul_sqrt2_sqrt3 = assertBool "" $ abs valP <= 0.0001
  where
    x = var X

    p :: UPolynomial Rational
    p = rootMul (x^2 - 2) (x^2 - 3)

    valP :: Double
    valP = eval (\X -> sqrt 2 * sqrt 3) $ mapCoeff fromRational p

case_rootNegate_test1 = assertBool "" $ abs valP <= 0.0001
  where
    x = var X

    p :: UPolynomial Rational
    p = rootScale (-1) (x^3 - 3)

    valP :: Double
    valP = eval (\X -> - (3 ** (1/3))) $ mapCoeff fromRational p

case_rootNegate_test2 = rootScale (-1) p @?= normalizePoly q
  where
    x :: UPolynomial Rational
    x = var X
    p = x^3 - 3
    q = x^3 + 3

case_rootNegate_test3 = rootScale (-1) p @?= normalizePoly q
  where
    x :: UPolynomial Rational
    x = var X
    p = (x-2)*(x-3)*(x-4)
    q = (x+2)*(x+3)*(x+4)

case_rootScale = rootScale 2 p @?= normalizePoly q
  where
    x :: UPolynomial Rational
    x = var X
    p = (x-2)*(x-3)*(x-4)
    q = (x-4)*(x-6)*(x-8)

case_rootScale_zero = rootScale 0 p @?= normalizePoly q
  where
    x :: UPolynomial Rational
    x = var X
    p = (x-2)*(x-3)*(x-4)
    q = x

case_rootRecip = assertBool "" $ abs valP <= 0.0001
  where
    x = var X

    p :: UPolynomial Rational
    p = rootRecip (x^3 - 3)

    valP :: Double
    valP = eval (\X -> 1 / (3 ** (1/3))) $ mapCoeff fromRational p

{--------------------------------------------------------------------
  algebraic reals
--------------------------------------------------------------------}

case_realRoots_zero = realRoots (0 :: UPolynomial Rational) @?= []

case_realRoots_nonminimal =
  realRoots ((x^2 - 1) * (x - 3)) @?= [-1,1,3]
  where
    x = var X

case_realRoots_minus_one = realRoots (x^2 + 1) @?= []
  where
    x = var X

case_realRoots_two = length (realRoots (x^2 - 2)) @?= 2
  where
    x = var X

case_realRoots_multipleRoots = length (realRoots (x^2 + 2*x + 1)) @?= 1
  where
    x = var X

case_eq = sqrt2*sqrt2 - 2 @?= 0

case_eq_refl = assertBool "" $ sqrt2 == sqrt2

case_diseq_1 = assertBool "" $ sqrt2 /= sqrt3

case_diseq_2 = assertBool "" $ sqrt2 /= neg_sqrt2

case_cmp_1 = assertBool "" $ 0 < sqrt2

case_cmp_2 = assertBool "" $ neg_sqrt2 < 0

case_cmp_3 = assertBool "" $ 0 < neg_sqrt2 * neg_sqrt2

case_cmp_4 = assertBool "" $ neg_sqrt2 * neg_sqrt2 * neg_sqrt2 < 0

case_floor_sqrt2 = floor sqrt2 @?= 1

case_floor_neg_sqrt2 = floor neg_sqrt2 @?= -2

case_floor_1 = floor 1 @?= 1

case_floor_neg_1 = floor (-1) @?= -1

case_ceiling_sqrt2 = ceiling sqrt2 @?= 2

case_ceiling_neg_sqrt2 = ceiling neg_sqrt2 @?= -1

case_ceiling_1 = ceiling 1 @?= 1

case_ceiling_neg_1 = ceiling (-1) @?= -1

case_round_sqrt2 = round sqrt2 @?= 1

case_toRational = toRational r @?= 3/2
  where
    x = var X
    [r] = realRoots (2*x - 3)

case_toRational_error = do
  r <- try $ evaluate $ toRational sqrt2
  case r of
    Left (e :: SomeException) -> return ()
    Right _ -> assertFailure "shuold be error"

-- 期待値は Wolfram Alpha で x^3 - Sqrt[2]*x + 3 を調べて Real root の exact form で得た
case_simpARealPoly = simpARealPoly p @?= q
  where
    x :: forall k. (Num k, Eq k) => UPolynomial k
    x = var X
    p = x^3 - constant sqrt2 * x + 3
    q = x^6 + 6*x^3 - 2*x^2 + 9

case_deg_sqrt2 = deg sqrt2 @?= 2

case_deg_neg_sqrt2 = deg neg_sqrt2 @?= 2

case_deg_sqrt2_minus_sqrt2 = deg (sqrt2 - sqrt2) @?= 1

case_deg_sqrt2_times_sqrt2 = deg (sqrt2 * sqrt2) @?= 1

case_isAlgebraicInteger_sqrt2 = isAlgebraicInteger sqrt2 @?= True

case_isAlgebraicInteger_neg_sqrt2 = isAlgebraicInteger neg_sqrt2 @?= True

case_isAlgebraicInteger_one_half = isAlgebraicInteger (1/2) @?= False

case_isAlgebraicInteger_one_sqrt2 = isAlgebraicInteger (1 / sqrt2) @?= False

case_height_sqrt2 = height sqrt2 @?= 2

case_height_10 = height 10 @?= 10

prop_approx_sqrt2 =
  forAll epsilons $ \epsilon ->
    abs (sqrt2 - fromRational (approx sqrt2 epsilon)) <= fromRational epsilon

prop_approxInterval_sqrt2 =
  forAll epsilons $ \epsilon ->
    Interval.width (approxInterval sqrt2 epsilon) <= epsilon

epsilons :: Gen Rational
epsilons = do
  r <- liftM abs $ arbitrary `suchThat` (0/=)
  if r > 0
     then return (1/r)
     else return r

------------------------------------------------------------------------
-- Test harness

main :: IO ()
main = $(defaultMainGenerator)
