{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

import Prelude hiding (lex)
import qualified Control.Exception as E
import Control.Monad
import qualified Data.FiniteField as FF
import Data.List
import Data.Ratio
import qualified Data.Set as Set
import qualified Data.Map as Map
import Test.Tasty
import Test.Tasty.QuickCheck
import Test.Tasty.HUnit
import Test.Tasty.TH
import Text.PrettyPrint.HughesPJClass

import ToySolver.Data.Polynomial (Polynomial, Term, Monomial, UPolynomial, UTerm, UMonomial, X (..))
import qualified ToySolver.Data.Polynomial as P
import qualified ToySolver.Data.Polynomial.GroebnerBasis as GB
import qualified ToySolver.Data.Polynomial.Factorization.FiniteField as FactorFF
import qualified ToySolver.Data.Polynomial.Factorization.Hensel.Internal as Hensel
import qualified ToySolver.Data.Polynomial.Factorization.Zassenhaus as Zassenhaus
import qualified ToySolver.Data.Polynomial.Interpolation.Lagrange as LagrangeInterpolation

import qualified Data.Interval as Interval
import Data.Interval (Interval, Extended (..), (<=..<=), (<..<=), (<=..<), (<..<))

{--------------------------------------------------------------------
  Polynomial type
--------------------------------------------------------------------}

prop_plus_comm =
  forAll polynomials $ \a ->
  forAll polynomials $ \b ->
    a + b == b + a

prop_plus_assoc =
  forAll polynomials $ \a ->
  forAll polynomials $ \b ->
  forAll polynomials $ \c ->
    a + (b + c) == (a + b) + c

prop_plus_unitL =
  forAll polynomials $ \a ->
    P.constant 0 + a == a

prop_plus_unitR =
  forAll polynomials $ \a ->
    a + P.constant 0 == a

prop_prod_comm =
  forAll polynomials $ \a ->
  forAll polynomials $ \b ->
    a * b == b * a

prop_prod_assoc =
  forAll polynomials $ \a ->
  forAll polynomials $ \b ->
  forAll polynomials $ \c ->
    a * (b * c) == (a * b) * c

prop_prod_unitL =
  forAll polynomials $ \a ->
    P.constant 1 * a == a

prop_prod_unitR =
  forAll polynomials $ \a ->
    a * P.constant 1 == a

prop_distL =
  forAll polynomials $ \a ->
  forAll polynomials $ \b ->
  forAll polynomials $ \c ->
    a * (b + c) == a * b + a * c

prop_distR =
  forAll polynomials $ \a ->
  forAll polynomials $ \b ->
  forAll polynomials $ \c ->
    (b + c) * a == b * a + c * a

prop_negate =
  forAll polynomials $ \a ->
    a + negate a == 0

prop_negate_involution =
  forAll polynomials $ \a ->
    negate (negate a) == a

prop_divModMP =
  forAll polynomials $ \g ->
    forAll (replicateM 3 polynomials) $ \fs ->
      all (0/=) fs ==>
        let (qs, r) = P.divModMP P.lex g fs
        in sum (zipWith (*) fs qs) + r == g

case_prettyShow_test1 =
  prettyShow p @?= "-x1^2*x2 + 3*x1 - 2*x2"
  where
    p :: Polynomial Rational Int
    p = - (P.var 1)^2 * P.var 2 + 3 * P.var 1 - 2 * P.var 2

case_prettyShow_test2 =
  prettyShow p @?= "(x0 + 1)*x"
  where
    p :: UPolynomial (Polynomial Rational Int)
    p = P.constant (P.var (0::Int) + 1) * P.var X

case_prettyShow_test3 =
  prettyShow p @?= "(-1)*x"
  where
    p :: UPolynomial (Polynomial Rational Int)
    p = P.constant (-1) * P.var X

case_prettyShow_test4 =
  prettyShow p @?= "x^2 - (1/2)"
  where
    p :: UPolynomial Rational
    p = (P.var X)^2 - P.constant (1/2)

case_deg_0 = assertBool "" $ (P.deg p < 0)
  where
    p :: UPolynomial Rational
    p = 0

{--------------------------------------------------------------------
  Univalent polynomials
--------------------------------------------------------------------}

prop_divMod =
  forAll upolynomials $ \a ->
  forAll upolynomials $ \b ->
    b /= 0 ==>
      let (q,r) = P.divMod a b
      in a == q*b + r && (r==0 || P.deg b > P.deg r)

case_divMod_1 =  g*q + r @?= f
  where
    x :: UPolynomial Rational
    x = P.var X
    f = x^3 + x^2 + x
    g = x^2 + 1
    (q,r) = f `P.divMod` g

prop_gcd_divisible =
  forAll upolynomials $ \a ->
  forAll upolynomials $ \b ->
    (a /= 0 && b /= 0) ==>
      let c = P.gcd a b
      in a `P.mod` c == 0 && b `P.mod` c == 0

prop_gcd_comm =
  forAll upolynomials $ \a ->
  forAll upolynomials $ \b ->
    P.gcd a b == P.gcd b a

prop_gcd_euclid =
  forAll upolynomials $ \p ->
  forAll upolynomials $ \q ->
  forAll upolynomials $ \r ->
    (p /= 0 && q /= 0 && r /= 0) ==>
      P.gcd p q == P.gcd p (q + p*r)

case_gcd_1 = P.gcd f1 f2 @?= 1
  where
    x :: UPolynomial Rational
    x = P.var X
    f1 = x^3 + x^2 + x
    f2 = x^2 + 1

prop_exgcd =
  forAll upolynomials $ \a ->
  forAll upolynomials $ \b ->
    let (g,u,v) = P.exgcd a b
    in a*u + b*v == g -- Bśzout's identity

case_exgcd_1 = P.exgcd p q @?= (expected_g, expected_u, expected_v)
  where
    x :: UPolynomial Rational
    x = P.var X
    p = x^4 - 3*x^3 + x^2 - x + 1
    q = 2*x^3 - x^2 + x + 3
    expected_g = 1
    expected_u = P.constant (94/2219) * x^2 + P.constant (9/317) * x + P.constant (404/2219)
    expected_v = P.constant (-47/2219) * x^3 + P.constant (86/2219) * x^2 - P.constant (88/2219) * x + P.constant (605/2219)

eqUpToInvElem :: UPolynomial Integer -> UPolynomial Integer -> Bool
eqUpToInvElem 0 0 = True
eqUpToInvElem _ 0 = False
eqUpToInvElem a b =
  case P.mapCoeff fromInteger a `P.divMod` P.mapCoeff fromInteger b of
    (q,r) -> r == 0 && P.deg q <= 0

prop_gcd'_comm =
  forAll upolynomialsZ $ \a ->
  forAll upolynomialsZ $ \b ->
    P.gcd' a b `eqUpToInvElem` P.gcd' b a

prop_gcd'_euclid =
  forAll upolynomialsZ $ \p ->
  forAll upolynomialsZ $ \q ->
  forAll upolynomialsZ $ \r ->
    (p /= 0 && q /= 0 && r /= 0) ==>
      P.gcd' p q `eqUpToInvElem` P.gcd' p (q + p*r)

case_gcd'_1 = eqUpToInvElem (P.gcd' f1 f2) 1 @?= True
  where
    x :: UPolynomial Integer
    x = P.var X
    f1 = x^3 + x^2 + x
    f2 = x^2 + 1

prop_lcm_divisible =
  forAll upolynomials $ \a ->
  forAll upolynomials $ \b ->
    (a /= 0 && b /= 0) ==>
      let c = P.lcm a b
      in c `P.mod` a == 0 && c `P.mod` b == 0

prop_lcm_comm =
  forAll upolynomials $ \a ->
  forAll upolynomials $ \b ->
    P.lcm a b == P.lcm b a

prop_deriv_integral =
  forAll upolynomials $ \a ->
    P.deriv (P.integral a x) x == a
  where
    x = X

prop_integral_deriv =
  forAll upolynomials $ \a ->
    P.deg (P.integral (P.deriv a x) x - a) <= 0
  where
    x = X

prop_pp_cont =
  forAll polynomials $ \p ->
    P.cont (P.pp p) == 1

prop_cont_prod =
  forAll polynomials $ \p ->
    forAll polynomials $ \q ->
      (p /= 0 && q /= 0) ==>
        P.cont (p*q) == P.cont p * P.cont q

case_cont_pp_Integer = do
  P.cont p @?= 5
  P.pp p   @?= (-2*x^2 + x + 1)
  where
    x = P.var X
    p :: UPolynomial Integer
    p = -10*x^2 + 5*x + 5

case_cont_pp_Rational = do
  P.cont p @?= 1/6
  P.pp p   @?= (2*x^5 + 21*x^2 + 12*x + 6)
  where
    x :: P.Var a X => a
    x = P.var X
    p :: UPolynomial Rational
    p = P.constant (1/3) * x^5 + P.constant (7/2) * x^2 + 2 * x + 1

prop_pdivMod =
  forAll upolynomialsZ $ \f ->
  forAll upolynomialsZ $ \g ->
    g /= 0 ==>
      let (b,q,r) = f `P.pdivMod` g
      in P.constant b * f == q*g + r && P.deg r < P.deg g

prop_pdiv =
  forAll upolynomialsZ $ \f ->
  forAll upolynomialsZ $ \g ->
    g /= 0 ==>
      let (_,q,_) = f `P.pdivMod` g
      in f `P.pdiv` g == q

prop_pmod =
  forAll upolynomialsZ $ \f ->
  forAll upolynomialsZ $ \g ->
    g /= 0 ==>
      let (_,_,r) = f `P.pdivMod` g
      in f `P.pmod` g == r

{--------------------------------------------------------------------
  Term
--------------------------------------------------------------------}

{--------------------------------------------------------------------
  Monic Monomial
--------------------------------------------------------------------}

prop_degreeOfProduct =
  forAll monicMonomials $ \a ->
  forAll monicMonomials $ \b ->
    P.deg (a `P.mmult` b) == P.deg a + P.deg b

prop_degreeOfUnit =
  P.deg P.mone == 0

prop_mmult_unitL =
  forAll monicMonomials $ \a ->
    P.mone `P.mmult` a == a

prop_mmult_unitR =
  forAll monicMonomials $ \a ->
    a `P.mmult` P.mone == a

prop_mmult_comm =
  forAll monicMonomials $ \a ->
  forAll monicMonomials $ \b ->
    a `P.mmult` b == b `P.mmult` a

prop_mmult_assoc =
  forAll monicMonomials $ \a ->
  forAll monicMonomials $ \b ->
  forAll monicMonomials $ \c ->
    a `P.mmult` (b `P.mmult` c) == (a `P.mmult` b) `P.mmult` c

prop_mmult_Divisible =
  forAll monicMonomials $ \a ->
  forAll monicMonomials $ \b ->
    let c = a `P.mmult` b
    in a `P.mdivides` c && b `P.mdivides` c

prop_mmult_Div =
  forAll monicMonomials $ \a ->
  forAll monicMonomials $ \b ->
    let c = a `P.mmult` b
    in c `P.mdiv` a == b && c `P.mdiv` b == a

case_mderiv = P.mderiv p 1 @?= (2, q)
  where
    p = P.mfromIndices [(1,2),(2,4)]
    q = P.mfromIndices [(1,1),(2,4)]

-- lcm (x1^2 * x2^4) (x1^3 * x2^1) = x1^3 * x2^4
case_mlcm = P.mlcm p1 p2 @?= P.mfromIndices [(1,3),(2,4)]
  where
    p1 = P.mfromIndices [(1,2),(2,4)]
    p2 = P.mfromIndices [(1,3),(2,1)]

-- gcd (x1^2 * x2^4) (x2^1 * x3^2) = x2
case_mgcd = P.mgcd p1 p2 @?= P.mfromIndices [(2,1)]
  where
    p1 = P.mfromIndices [(1,2),(2,4)]
    p2 = P.mfromIndices [(2,1),(3,2)]

prop_mlcm_divisible =
  forAll monicMonomials $ \a ->
  forAll monicMonomials $ \b ->
    let c = P.mlcm a b
    in a `P.mdivides` c && b `P.mdivides` c

prop_mgcd_divisible =
  forAll monicMonomials $ \a ->
  forAll monicMonomials $ \b ->
    let c = P.mgcd a b
    in c `P.mdivides` a && c `P.mdivides` b

{--------------------------------------------------------------------
  Monomial Order
--------------------------------------------------------------------}

-- http://en.wikipedia.org/wiki/Monomial_order
case_lex = sortBy P.lex [a,b,c,d] @?= [b,a,d,c]
  where
    x = 1
    y = 2
    z = 3
    a = P.mfromIndices [(x,1),(y,2),(z,1)]
    b = P.mfromIndices [(z,2)]
    c = P.mfromIndices [(x,3)]
    d = P.mfromIndices [(x,2),(z,2)]

-- http://en.wikipedia.org/wiki/Monomial_order
case_grlex = sortBy P.grlex [a,b,c,d] @?= [b,c,a,d]
  where
    x = 1
    y = 2
    z = 3
    a = P.mfromIndices [(x,1),(y,2),(z,1)]
    b = P.mfromIndices [(z,2)]
    c = P.mfromIndices [(x,3)]
    d = P.mfromIndices [(x,2),(z,2)]

-- http://en.wikipedia.org/wiki/Monomial_order
case_grevlex = sortBy P.grevlex [a,b,c,d] @?= [b,c,d,a]
  where
    x = 1
    y = 2
    z = 3
    a = P.mfromIndices [(x,1),(y,2),(z,1)]
    b = P.mfromIndices [(z,2)]
    c = P.mfromIndices [(x,3)]
    d = P.mfromIndices [(x,2),(z,2)]

prop_refl_lex     = propRefl P.lex
prop_refl_grlex   = propRefl P.grlex
prop_refl_grevlex = propRefl P.grevlex

prop_trans_lex     = propTrans P.lex
prop_trans_grlex   = propTrans P.grlex
prop_trans_grevlex = propTrans P.grevlex

prop_sym_lex     = propSym P.lex
prop_sym_grlex   = propSym P.grlex
prop_sym_grevlex = propSym P.grevlex

prop_monomial_order_property1_lex     = monomialOrderProp1 P.lex
prop_monomial_order_property1_grlex   = monomialOrderProp1 P.grlex
prop_monomial_order_property1_grevlex = monomialOrderProp1 P.grevlex

prop_monomial_order_property2_lex     = monomialOrderProp2 P.lex
prop_monomial_order_property2_grlex   = monomialOrderProp2 P.grlex
prop_monomial_order_property2_grevlex = monomialOrderProp2 P.grevlex

propRefl cmp =
  forAll monicMonomials $ \a -> cmp a a == EQ

propTrans cmp =
  forAll monicMonomials $ \a ->
  forAll monicMonomials $ \b ->
    cmp a b == LT ==>
      forAll monicMonomials $ \c ->
        cmp b c == LT ==> cmp a c == LT

propSym cmp =
  forAll monicMonomials $ \a ->
  forAll monicMonomials $ \b ->
    cmp a b == flipOrdering (cmp b a)
  where
    flipOrdering EQ = EQ
    flipOrdering LT = GT
    flipOrdering GT = LT

monomialOrderProp1 cmp =
  forAll monicMonomials $ \a ->
  forAll monicMonomials $ \b ->
    let r = cmp a b
    in cmp a b /= EQ ==>
         forAll monicMonomials $ \c ->
           cmp (a `P.mmult` c) (b `P.mmult` c) == r

monomialOrderProp2 cmp =
  forAll monicMonomials $ \a ->
    a /= P.mone ==> cmp P.mone a == LT

{--------------------------------------------------------------------
-- Gröbner basis
--------------------------------------------------------------------}

-- http://math.rice.edu/~cbruun/vigre/vigreHW6.pdf
-- Example 1
case_spolynomial = GB.spolynomial P.grlex f g @?= - x^3*y^3 - P.constant (1/3) * y^3 + x^2
  where
    x = P.var 1
    y = P.var 2
    f, g :: Polynomial Rational Int
    f = x^3*y^2 - x^2*y^3 + x
    g = 3*x^4*y + y^2


-- http://math.rice.edu/~cbruun/vigre/vigreHW6.pdf
-- Exercise 1
case_buchberger1 = Set.fromList gb @?= Set.fromList expected
  where
    gb = GB.basis P.lex [x^2-y, x^3-z]
    expected = [y^3 - z^2, x^2 - y, x*z - y^2, x*y - z]

    x :: Polynomial Rational Int
    x = P.var 1
    y = P.var 2
    z = P.var 3

-- http://math.rice.edu/~cbruun/vigre/vigreHW6.pdf
-- Exercise 2
case_buchberger2 = Set.fromList gb @?= Set.fromList expected
  where
    gb = GB.basis P.grlex [x^3-2*x*y, x^2*y-2*y^2+x]
    expected = [x^2, x*y, y^2 - P.constant (1/2) * x]

    x :: Polynomial Rational Int
    x = P.var 1
    y = P.var 2

-- http://www.iisdavinci.it/jeometry/buchberger.html
case_buchberger3 = Set.fromList gb @?= Set.fromList expected
  where
    gb = GB.basis P.lex [x^2+2*x*y^2, x*y+2*y^3-1]
    expected = [x, y^3 - P.constant (1/2)]
    x :: Polynomial Rational Int
    x = P.var 1
    y = P.var 2

-- http://www.orcca.on.ca/~reid/NewWeb/DetResDes/node4.html
-- 時間がかかるので自動実行されるテストケースには含めていない
disabled_case_buchberger4 = Set.fromList gb @?= Set.fromList expected
  where
    x :: Polynomial Rational Int
    x = P.var 1
    y = P.var 2
    z = P.var 3

    gb = GB.basis P.lex [x^2+y*z-2, x*z+y^2-3, x*y+z^2-5]

    expected = GB.reduceGBasis P.lex $
      [ 8*z^8-100*z^6+438*z^4-760*z^2+361
      , 361*y+8*z^7+52*z^5-740*z^3+1425*z
      , 361*x-88*z^7+872*z^5-2690*z^3+2375*z
      ]
{-
Risa/Asir での結果

load("gr");
gr([x^2+y*z-2, x*z+y^2-3, x*y+z^2-5],[x,y,z], 2);

[8*z^8-100*z^6+438*z^4-760*z^2+361,
361*y+8*z^7+52*z^5-740*z^3+1425*z,
361*x-88*z^7+872*z^5-2690*z^3+2375*z]
-}

-- Seven Trees in One
-- http://arxiv.org/abs/math/9405205
case_Seven_Trees_in_One = P.reduce P.lex (x^7 - x) gb @?= 0
  where
    x :: Polynomial Rational Int
    x = P.var 1
    gb = GB.basis P.lex [x-(x^2 + 1)]

-- Non-linear loop invariant generation using Gröbner bases
-- http://portal.acm.org/citation.cfm?id=964028
-- http://www-step.stanford.edu/papers/popl04.pdf
-- Example 3
-- Consider again the ideal from Example 2; I = {f : x^2-y, g : y-z, h
-- : x+z}.  The Gröbner basis for I is G = {f' : z^2-z, g : y-z, h :
-- x+z}. With this basis, every reduction of p : x^2 - y^2 will yield
-- a normal form 0.
case_sankaranarayanan04nonlinear = do
  Set.fromList gb @?= Set.fromList [f', g, h]
  P.reduce P.lex (x^2 - y^2) gb @?= 0
  where
    x :: Polynomial Rational Int
    x = P.var 1
    y = P.var 2
    z = P.var 3
    f = x^2 - y
    g = y - z
    h = x + z
    f' = z^2 - z
    gb = GB.basis P.lex [f, g, h]

{--------------------------------------------------------------------
  Generators
--------------------------------------------------------------------}

monicMonomials :: Gen (Monomial Int)
monicMonomials = do
  size <- choose (0, 3)
  xs <- replicateM size $ do
    v <- choose (-5, 5)
    e <- liftM ((+1) . abs) arbitrary
    return $ P.var v `P.mpow` e
  return $ foldl' P.mmult P.mone xs

genTerms :: Gen (Term Rational Int)
genTerms = do
  m <- monicMonomials
  c <- arbitrary
  return (c,m)

polynomials :: Gen (Polynomial Rational Int)
polynomials = do
  size <- choose (0, 5)
  xs <- replicateM size genTerms
  return $ sum $ map P.fromTerm xs

umonicMonomials :: Gen UMonomial
umonicMonomials = do
  size <- choose (0, 3)
  xs <- replicateM size $ do
    e <- choose (1, 4)
    return $ P.var X `P.mpow` e
  return $ foldl' P.mmult P.mone xs

genUTerms :: Gen (UTerm Rational)
genUTerms = do
  m <- umonicMonomials
  c <- arbitrary
  return (c,m)

upolynomials :: Gen (UPolynomial Rational)
upolynomials = do
  size <- choose (0, 5)
  xs <- replicateM size genUTerms
  return $ sum $ map P.fromTerm xs

genUTermsZ :: Gen (UTerm Integer)
genUTermsZ = do
  m <- umonicMonomials
  c <- arbitrary
  return (c,m)

upolynomialsZ :: Gen (UPolynomial Integer)
upolynomialsZ = do
  size <- choose (0, 5)
  xs <- replicateM size genUTermsZ
  return $ sum $ map P.fromTerm xs

------------------------------------------------------------------------

case_factorZ_zero = P.factor (0::UPolynomial Integer) @?= [(0,1)]
case_factorZ_one  = P.factor (1::UPolynomial Integer) @?= []
case_factorZ_two  = P.factor (2::UPolynomial Integer) @?= [(2,1)]

-- http://en.wikipedia.org/wiki/Factorization_of_polynomials
case_factorZ_test1 = do
  sort actual @?= sort expected
  product [g^n | (g,n) <- actual] @?= f
  where
    x :: UPolynomial Integer
    x = P.var X
    f = 2*(x^5 + x^4 + x^2 + x + 2)
    actual   = P.factor f
    expected = [(2,1), (x^2+x+1,1), (x^3-x+2,1)]

case_factorZ_test2 = do
  sort actual @?= sort expected
  product [g^n | (g,n) <- actual] @?= f
  where
    x :: UPolynomial Integer
    x = P.var X
    f = - (x^5 + x^4 + x^2 + x + 2)
    actual   = P.factor f
    expected = [(-1,1), (x^2+x+1,1), (x^3-x+2,1)]

case_factorQ_zero = P.factor (0::UPolynomial Rational) @?= [(0,1)]
case_factorQ_one  = P.factor (1::UPolynomial Rational) @?= []
case_factorQ_two  = P.factor (2::UPolynomial Rational) @?= [(2,1)]

-- http://en.wikipedia.org/wiki/Factorization_of_polynomials
case_factorQ_test1 = do
  sort actual @?= sort expected
  product [g^n | (g,n) <- actual] @?= f
  where
    x :: UPolynomial Rational
    x = P.var X
    f = 2*(x^5 + x^4 + x^2 + x + 2)
    actual   = P.factor f
    expected = [(2, 1), (x^2+x+1, 1), (x^3-x+2, 1)]

case_factorQ_test2 = do
  sort actual @?= sort expected
  product [g^n | (g,n) <- actual] @?= f
  where
    x :: UPolynomial Rational
    x = P.var X
    f = - (x^5 + x^4 + x^2 + x + 2)
    actual   = P.factor f
    expected = [(-1,1), (x^2+x+1,1), (x^3-x+2,1)]

-- http://en.wikipedia.org/wiki/Factorization_of_polynomials_over_a_finite_field_and_irreducibility_tests
case_FF_sqfree_test1 = do
  sort actual @?= sort expected
  product [f^n | (f,n) <- actual] @?= f
  where
    x :: UPolynomial $(FF.primeField 3)
    x = P.var X
    f  = x^11 + 2*x^9 + 2*x^8 + x^6 + x^5 + 2*x^3 + 2*x^2 + 1
    actual   = P.sqfree f
    expected = [(x+1, 1), (x^2+1, 3), (x+2, 4)]

{-
from "Computational Commutative Algebra 1" (Martin Kreuzer and Lorenzo Robbiano) pp.40

Risa/Asir
> load("fff");
> setmod_ff(5);
> fctr_ff(x^100 - x^200);
[[1*x+1,25],[1*x+3,25],[1*x+2,25],[1*x+4,25],[1*x,100]]
-}
case_FF_berlekamp_1 = do
  sort actual @?= sort expected
  product [g^n | (g,n) <- actual] @?= f
  where
    x :: UPolynomial $(FF.primeField 5)
    x = P.var X
    f = x^100 - x^200
    actual   = P.factor f
    expected = (4,1) : [(1*x+1,25), (1*x+3,25), (1*x+2,25), (1*x+4,25), (1*x,100)]

{-
from "Computational Commutative Algebra 1" (Martin Kreuzer and Lorenzo Robbiano) pp.40

Risa/Asir
> load("fff");
> setmod_ff(2);
> fctr_ff(1 + x + x^2 + x^6 + x^7 + x^8 + x^12);
[[1*x^5+1*x^3+1*x^2+1*x+1,1],[1*x^7+1*x^5+1*x^4+1*x^3+1,1]]*/
-}
case_FF_berlekamp_2 = do
  sort actual @?= sort expected
  product actual @?= f
  where
    x :: UPolynomial $(FF.primeField 2)
    x = P.var X
    f = 1 + x + x^2 + x^6 + x^7 + x^8 + x^12
    actual   = FactorFF.berlekamp f
    expected = [1*x^5+1*x^3+1*x^2+1*x+1, 1*x^7+1*x^5+1*x^4+1*x^3+1]

{-
from "Computational Commutative Algebra 1" (Martin Kreuzer and Lorenzo Robbiano) pp.40

Risa/Asir
> load("fff");
> setmod_ff(7);
> fctr_ff(1 - x^100);
[[1*x+1,1],[1*x+6,1],[1*x^2+1,1],[1*x^4+2*x^3+5*x^2+2*x+1,1],[1*x^4+5*x^3+5*x^2+5*x+1,1],[1*x^4+5*x^3+3*x^2+2*x+1,1],[1*x^4+2*x^3+3*x^2+5*x+1,1],[1*x^4+1*x^3+1*x^2+6*x+1,1],[1*x^4+1*x^3+5*x^2+1*x+1,1],[1*x^4+2*x^3+4*x^2+2*x+1,1],[1*x^4+3*x^3+6*x^2+4*x+1,1],[1*x^4+3*x^3+3*x+1,1],[1*x^4+5*x^3+2*x+1,1],[1*x^4+3*x^3+3*x^2+3*x+1,1],[1*x^4+6*x^3+5*x^2+6*x+1,1],[1*x^4+6*x^3+1*x^2+1*x+1,1],[1*x^4+4*x^3+3*x^2+4*x+1,1],[1*x^4+6*x^3+1*x^2+6*x+1,1],[1*x^4+4*x^3+4*x+1,1],[1*x^4+2*x^3+1*x^2+5*x+1,1],[1*x^4+5*x^3+4*x^2+5*x+1,1],[1*x^4+4*x^3+4*x^2+3*x+1,1],[1*x^4+5*x^3+1*x^2+2*x+1,1],[1*x^4+1*x^3+1*x^2+1*x+1,1],[1*x^4+3*x^3+4*x^2+4*x+1,1],[1*x^4+2*x^3+5*x+1,1],[1*x^4+4*x^3+6*x^2+3*x+1,1]]
-}
case_FF_berlekamp_3 = do
  sort actual @?= sort expected
  product [g^n | (g,n) <- actual] @?= f
  where
    x :: UPolynomial $(FF.primeField 7)
    x = P.var X
    f = 1 - x^100
    actual   = P.factor f
    expected = (6,1) : [(1*x+1,1), (1*x+6,1), (1*x^2+1,1), (1*x^4+2*x^3+5*x^2+2*x+1,1), (1*x^4+5*x^3+5*x^2+5*x+1,1), (1*x^4+5*x^3+3*x^2+2*x+1,1), (1*x^4+2*x^3+3*x^2+5*x+1,1), (1*x^4+1*x^3+1*x^2+6*x+1,1), (1*x^4+1*x^3+5*x^2+1*x+1,1), (1*x^4+2*x^3+4*x^2+2*x+1,1), (1*x^4+3*x^3+6*x^2+4*x+1,1), (1*x^4+3*x^3+3*x+1,1), (1*x^4+5*x^3+2*x+1,1), (1*x^4+3*x^3+3*x^2+3*x+1,1), (1*x^4+6*x^3+5*x^2+6*x+1,1), (1*x^4+6*x^3+1*x^2+1*x+1,1), (1*x^4+4*x^3+3*x^2+4*x+1,1), (1*x^4+6*x^3+1*x^2+6*x+1,1), (1*x^4+4*x^3+4*x+1,1), (1*x^4+2*x^3+1*x^2+5*x+1,1), (1*x^4+5*x^3+4*x^2+5*x+1,1), (1*x^4+4*x^3+4*x^2+3*x+1,1), (1*x^4+5*x^3+1*x^2+2*x+1,1), (1*x^4+1*x^3+1*x^2+1*x+1,1), (1*x^4+3*x^3+4*x^2+4*x+1,1), (1*x^4+2*x^3+5*x+1,1), (1*x^4+4*x^3+6*x^2+3*x+1,1)]

{-
from "Computational Commutative Algebra 1" (Martin Kreuzer and Lorenzo Robbiano) pp.40

Risa/Asir
> load("fff");
> setmod_ff(13);
> fctr_ff(8 + 2*x + 8*x^2 + 10*x^3 + 10*x^4 + x^6 +x^8);
[[1*x+3,1],[1*x^3+8*x^2+4*x+12,1],[1*x^4+2*x^3+3*x^2+4*x+6,1]]
-}
case_FF_berlekamp_4 = do
  sort actual @?= sort expected
  product actual @?= f
  where
    x :: UPolynomial $(FF.primeField 13)
    x = P.var X
    f = 8 + 2*x + 8*x^2 + 10*x^3 + 10*x^4 + x^6 +x^8
    actual   = FactorFF.berlekamp f
    expected = [1*x+3, 1*x^3+8*x^2+4*x+12, 1*x^4+2*x^3+3*x^2+4*x+6]

{-
from "Computational Commutative Algebra 1" (Martin Kreuzer and Lorenzo Robbiano) pp.40

Risa/Asir
> load("fff");
> setmod_ff(31991);
> fctr_ff(2 + x + x^2 + x^3 + x^4 + x^5);
[[1*x+13077,1],[1*x^4+18915*x^3+2958*x^2+27345*x+4834,1]]
-}
-- case_FF_berlekamp_5 = do
--   sort actual @?= sort expected
--   product actual @?= f
--   where
--     x :: UPolynomial $(FF.primeField 31991)
--     x = P.var X
--     f = 2 + x + x^2 + x^3 + x^4 + x^5
--     actual   = FactorFF.berlekamp f
--     expected = [1*x+13077, 1*x^4+18915*x^3+2958*x^2+27345*x+4834]


case_basisOfBerlekampSubalgebra_1 = sequence_ [(g ^ (5::Int)) `P.mod` f @?= g | g <- basis]
  where
    x :: UPolynomial $(FF.primeField 5)
    x = P.var X
    f = P.toMonic P.grlex $ x^100 - x^200
    basis = FactorFF.basisOfBerlekampSubalgebra f

case_basisOfBerlekampSubalgebra_2 = sequence_ [(g ^ (2::Int)) `P.mod` f @?= g | g <- basis]
  where
    x :: UPolynomial $(FF.primeField 2)
    x = P.var X
    f = 1 + x + x^2 + x^6 + x^7 + x^8 + x^12
    basis = FactorFF.basisOfBerlekampSubalgebra f

case_basisOfBerlekampSubalgebra_3 = sequence_ [(g ^ (2::Int)) `P.mod` f @?= g | g <- basis]
  where
    x :: UPolynomial $(FF.primeField 2)
    x = P.var X
    f = P.toMonic P.grlex $ 1 - x^100
    basis = FactorFF.basisOfBerlekampSubalgebra f


case_basisOfBerlekampSubalgebra_4 = sequence_ [(g ^ (13::Int)) `P.mod` f @?= g | g <- basis]
  where
    x :: UPolynomial $(FF.primeField 13)
    x = P.var X
    f = 8 + 2*x + 8*x^2 + 10*x^3 + 10*x^4 + x^6 +x^8
    basis = FactorFF.basisOfBerlekampSubalgebra f

-- case_basisOfBerlekampSubalgebra_5 = sequence_ [(g ^ (31991::Int)) `P.mod` f @?= g | g <- basis]
--   where
--     x :: UPolynomial $(FF.primeField 31991)
--     x = P.var X
--     f = 2 + x + x^2 + x^3 + x^4 + x^5
--     basis = FactorFF.basisOfBerlekampSubalgebra f

case_sqfree_Integer = actual @?= expected
  where
    x :: UPolynomial Integer
    x = P.var X
    actual   = P.sqfree (x^(2::Int) + 2*x + 1)
    expected = [(x + 1, 2)]

case_sqfree_Rational = actual @?= expected
  where
    x :: UPolynomial Rational
    x = P.var X
    actual   = P.sqfree (x^(2::Int) + 2*x + 1)
    expected = [(x + 1, 2)]

------------------------------------------------------------------------

-- http://www14.in.tum.de/konferenzen/Jass07/courses/1/Bulwahn/Buhlwahn_Paper.pdf
case_Hensel_Lifting :: Assertion
case_Hensel_Lifting = do
  Hensel.hensel f fs 2 @?= [x^(2::Int) + 5*x + 18, x + 5]
  Hensel.hensel f fs 3 @?= [x^(2::Int) + 105*x + 43, x + 30]
  Hensel.hensel f fs 4 @?= [x^(2::Int) + 605*x + 168, x + 30]
  where
    x :: forall k. (Eq k, Num k) => UPolynomial k
    x  = P.var X
    f :: UPolynomial Integer
    f  = x^(3::Int) + 10*x^(2::Int) - 432*x + 5040
    fs :: [UPolynomial $(FF.primeField 5)]
    fs = [x^(2::Int)+3, x]

case_cabook_proposition_5_10 :: Assertion
case_cabook_proposition_5_10 =
  sum [ei * (product fs `P.div` fi) | (ei,fi) <- zip es fs] @?= 1
  where
    x :: UPolynomial Rational
    x = P.var P.X
    fs = [x, x+1, x+2]
    es = Hensel.cabook_proposition_5_10 fs

case_cabook_proposition_5_11 :: Assertion
case_cabook_proposition_5_11 =
  sum [ei * (product fs `P.div` fi) | (ei,fi) <- zip es fs] @?= g
  where
    x :: UPolynomial Rational
    x = P.var P.X
    fs = [x, x+1, x+2]
    g  = x^(2::Int) + 1
    es = Hensel.cabook_proposition_5_11 fs g

------------------------------------------------------------------------

case_Zassenhaus_factor :: Assertion
case_Zassenhaus_factor = actual @?= expected
  where
    x :: UPolynomial Integer
    x = P.var X
    f = - (x^(5::Int) + x^(4::Int) + x^(2::Int) + x + 2)
    actual, expected :: [(UPolynomial Integer, Integer)]
    actual   = sort $ Zassenhaus.factor f
    expected = sort $ [(-1,1), (x^(2::Int)+x+1,1), (x^(3::Int)-x+2,1)]

case_Zassenhaus_zassenhaus_1 :: Assertion
case_Zassenhaus_zassenhaus_1 = actual @?= expected
  where
    x = P.var X
    f = x^(4::Int) + 4
    actual, expected :: [UPolynomial Integer]
    actual   = sort $ Zassenhaus.zassenhaus f
    expected = sort $ [x^(2::Int)+2*x+2, x^(2::Int)-2*x+2]

case_Zassenhaus_zassenhaus_2 :: Assertion
case_Zassenhaus_zassenhaus_2 = actual @?= expected
  where
    x = P.var X
    f = x^(9::Int) - 15*x^(6::Int) - 87*x^(3::Int) - 125
    actual, expected :: [UPolynomial Integer]
    actual   = sort $ Zassenhaus.zassenhaus f
    expected = sort $ [f]

------------------------------------------------------------------------

-- http://en.wikipedia.org/wiki/Lagrange_polynomial
case_Lagrange_interpolation_1 = p @?= q
  where
    x :: UPolynomial Rational
    x = P.var X
    p = LagrangeInterpolation.interpolate
        [ (1, 1)
        , (2, 4)
        , (3, 9)
        ]
    q = x^2

-- http://en.wikipedia.org/wiki/Lagrange_polynomial
case_Lagrange_interpolation_2 = p @?= q
  where
    x :: UPolynomial Rational
    x = P.var X
    p = LagrangeInterpolation.interpolate
        [ (1, 1)
        , (2, 8)
        , (3, 27)
        ]
    q = 6*x^2 - 11*x + 6

-- ---------------------------------------------------------------------

-- http://www.math.tamu.edu/~geller/factoring.pdf
case_eisensteinsCriterion_1 = P.eisensteinsCriterion p @?= True
  where
    x :: UPolynomial Rational
    x = P.var X
    p = 2*x^17 - 18*x^12 + 24*x^9 + 243*x^6 - 30*x^3 - 6

------------------------------------------------------------------------
-- Test harness

main :: IO ()
main = $(defaultMainGenerator)
