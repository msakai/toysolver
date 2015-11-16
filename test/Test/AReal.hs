{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
module Test.AReal (arealTestGroup) where

import Data.Maybe
import Data.Ratio
import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit
import Test.Tasty.TH

import ToySolver.Data.Polynomial (UPolynomial, X (..))
import qualified ToySolver.Data.Polynomial as P
import qualified ToySolver.Data.AlgebraicNumber.Sturm as Sturm
import ToySolver.Data.AlgebraicNumber.Real
import ToySolver.Data.AlgebraicNumber.Root

import Data.Interval (Interval, Extended (..), (<=..<=), (<..<=), (<=..<), (<..<))
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
    x = P.var X

-- ±√3
sqrt3 :: AReal
[neg_sqrt3, sqrt3] = realRoots (x^2 - 3)
  where
    x = P.var X

{--------------------------------------------------------------------
  root manipulation
--------------------------------------------------------------------}

case_rootAdd_sqrt2_sqrt3 = assertBool "" $ abs valP <= 0.0001
  where
    x = P.var X

    p :: UPolynomial Rational
    p = rootAdd (x^2 - 2) (x^2 - 3)

    valP :: Double
    valP = P.eval (\X -> sqrt 2 + sqrt 3) $ P.mapCoeff fromRational p

-- bug?
sample_rootAdd = p
  where
    x = P.var X    
    p :: UPolynomial Rational
    p = rootAdd (x^2 - 2) (x^6 + 6*x^3 - 2*x^2 + 9)

case_rootSub_sqrt2_sqrt3 = assertBool "" $ abs valP <= 0.0001
  where
    x = P.var X

    p :: UPolynomial Rational
    p = rootAdd (x^2 - 2) (rootScale (-1) (x^2 - 3))

    valP :: Double
    valP = P.eval (\X -> sqrt 2 - sqrt 3) $ P.mapCoeff fromRational p

case_rootMul_sqrt2_sqrt3 = assertBool "" $ abs valP <= 0.0001
  where
    x = P.var X

    p :: UPolynomial Rational
    p = rootMul (x^2 - 2) (x^2 - 3)

    valP :: Double
    valP = P.eval (\X -> sqrt 2 * sqrt 3) $ P.mapCoeff fromRational p

case_rootNegate_test1 = assertBool "" $ abs valP <= 0.0001
  where
    x = P.var X

    p :: UPolynomial Rational
    p = rootScale (-1) (x^3 - 3)

    valP :: Double
    valP = P.eval (\X -> - (3 ** (1/3))) $ P.mapCoeff fromRational p

case_rootNegate_test2 = rootScale (-1) p @?= normalizePoly q
  where
    x :: UPolynomial Rational
    x = P.var X
    p = x^3 - 3
    q = x^3 + 3

case_rootNegate_test3 = rootScale (-1) p @?= normalizePoly q
  where
    x :: UPolynomial Rational
    x = P.var X
    p = (x-2)*(x-3)*(x-4)
    q = (x+2)*(x+3)*(x+4)

case_rootScale = rootScale 2 p @?= normalizePoly q
  where
    x :: UPolynomial Rational
    x = P.var X
    p = (x-2)*(x-3)*(x-4)
    q = (x-4)*(x-6)*(x-8)

case_rootScale_zero = rootScale 0 p @?= normalizePoly q
  where
    x :: UPolynomial Rational
    x = P.var X
    p = (x-2)*(x-3)*(x-4)
    q = x

case_rootRecip = assertBool "" $ abs valP <= 0.0001
  where
    x = P.var X

    p :: UPolynomial Rational
    p = rootRecip (x^3 - 3)

    valP :: Double
    valP = P.eval (\X -> 1 / (3 ** (1/3))) $ P.mapCoeff fromRational p

{--------------------------------------------------------------------
  algebraic reals
--------------------------------------------------------------------}

case_realRoots_zero = realRoots (0 :: UPolynomial Rational) @?= []

case_realRoots_nonminimal =
  realRoots ((x^2 - 1) * (x - 3)) @?= [-1,1,3]
  where
    x = P.var X

case_realRoots_minus_one = realRoots (x^2 + 1) @?= []
  where
    x = P.var X

case_realRoots_two = length (realRoots (x^2 - 2)) @?= 2
  where
    x = P.var X

case_realRoots_multipleRoots = length (realRoots (x^2 + 2*x + 1)) @?= 1
  where
    x = P.var X

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
    x = P.var X
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
    x = P.var X
    p = x^3 - P.constant sqrt2 * x + 3
    q = x^6 + 6*x^3 - 2*x^2 + 9

case_deg_sqrt2 = P.deg sqrt2 @?= 2

case_deg_neg_sqrt2 = P.deg neg_sqrt2 @?= 2

case_deg_sqrt2_minus_sqrt2 = P.deg (sqrt2 - sqrt2) @?= 1

case_deg_sqrt2_times_sqrt2 = P.deg (sqrt2 * sqrt2) @?= 1

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

-- http://mathworld.wolfram.com/SturmFunction.html
case_sturmChain = Sturm.sturmChain p0 @?= chain
  where
    x = P.var X
    p0 = x^5 - 3*x - 1
    p1 = 5*x^4 - 3
    p2 = P.constant (1/5) * (12*x + 5)
    p3 = P.constant (59083 / 20736)
    chain = [p0, p1, p2, p3]

-- http://mathworld.wolfram.com/SturmFunction.html
case_numRoots_1 =
  sequence_
  [ Sturm.numRoots p (Finite (-2)   <=..<= Finite 0)      @?= 2
  , Sturm.numRoots p (Finite 0      <=..<= Finite 2)      @?= 1
  , Sturm.numRoots p (Finite (-1.5) <=..<= Finite (-1.0)) @?= 1
  , Sturm.numRoots p (Finite (-0.5) <=..<= Finite 0)      @?= 1
  , Sturm.numRoots p (Finite 1      <=..<= Finite (1.5))  @?= 1
  ]
  where
    x = P.var X
    p = x^5 - 3*x - 1

-- check interpretation of intervals
case_numRoots_2 =
  sequence_
  [ Sturm.numRoots p (Finite 2 <..<=  Finite 3) @?= 0
  , Sturm.numRoots p (Finite 2 <=..<= Finite 3) @?= 1
  , Sturm.numRoots p (Finite 1 <..<   Finite 2) @?= 0
  , Sturm.numRoots p (Finite 1 <..<=  Finite 2) @?= 1
  ]
  where
    x = P.var X
    p = x^2 - 4

case_separate = do
  forM_ (zip vals intervals) $ \(v,ival) -> do
    Interval.member v ival @?= True
    forM_ (filter (v/=) vals) $ \v2 -> do
      Interval.member v2 ival @?= False
  where
    x = P.var X
    p = x^5 - 3*x - 1
    intervals = Sturm.separate p
    vals = [-1.21465, -0.334734, 1.38879]

------------------------------------------------------------------------
-- Test harness

arealTestGroup :: TestTree
arealTestGroup = $(testGroupGenerator)
