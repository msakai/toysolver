{-# LANGUAGE TemplateHaskell #-}

import Prelude hiding (lex)
import Control.Monad
import qualified Data.FiniteField as FF
import Data.List
import Data.Ratio
import qualified Data.Set as Set
import qualified Data.Map as Map
import Test.HUnit hiding (Test)
import Test.QuickCheck
import Test.Framework (Test, defaultMain, testGroup)
import Test.Framework.TH
import Test.Framework.Providers.HUnit
import Test.Framework.Providers.QuickCheck2
import Text.PrettyPrint.HughesPJClass

import Data.Polynomial
import qualified Data.Polynomial.GBasis as GB
import Data.Polynomial.RootSeparation.Sturm
import qualified Data.Polynomial.Factorization.FiniteField as FactorFF
import qualified Data.Polynomial.Factorization.Integer as FactorZ
import qualified Data.Polynomial.Factorization.Rational as FactorQ
import qualified Data.Polynomial.Interpolation.Lagrange as LagrangeInterpolation
import qualified Data.Interval as Interval
import Data.Interval (Interval, EndPoint (..), (<=..<=), (<..<=), (<=..<), (<..<))

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
    constant 0 + a == a

prop_plus_unitR = 
  forAll polynomials $ \a ->
    a + constant 0 == a

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
    constant 1 * a == a

prop_prod_unitR = 
  forAll polynomials $ \a ->
    a * constant 1 == a

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

prop_polyMDivMod =
  forAll polynomials $ \g ->
    forAll (replicateM 3 polynomials) $ \fs ->
      all (0/=) fs ==>
        let (qs, r) = polyMDivMod lex g fs
        in sum (zipWith (*) fs qs) + r == g

case_prettyShow_test1 =
  prettyShow p @?= "-x1^2*x2 + 3*x1 - 2*x2"
  where
    p :: Polynomial Rational Int
    p = - (var 1)^2 * var 2 + 3 * var 1 - 2 * var 2

case_prettyShow_test2 =
  prettyShow p @?= "(x0 + 1)*x"
  where
    p :: UPolynomial (Polynomial Rational Int)
    p = constant (var (0::Int) + 1) * var X

case_prettyShow_test3 =
  prettyShow p @?= "(-1)*x"
  where
    p :: UPolynomial (Polynomial Rational Int)
    p = constant (-1) * var X

case_prettyShow_test4 =
  prettyShow p @?= "x^2 - (1/2)"
  where
    p :: UPolynomial Rational
    p = (var X)^2 - constant (1/2)

case_deg_0 = assertBool "" $ (deg p < 0)
  where
    p :: UPolynomial Rational
    p = 0

{--------------------------------------------------------------------
  Univalent polynomials
--------------------------------------------------------------------}

prop_polyDivMod =
  forAll upolynomials $ \a ->
  forAll upolynomials $ \b ->
    b /= 0 ==> 
      let (q,r) = polyDivMod a b
      in a == q*b + r && (r==0 || deg b > deg r)

case_polyDivMod_1 =  g*q + r @?= f
  where
    x :: UPolynomial Rational
    x = var X
    f = x^3 + x^2 + x
    g = x^2 + 1
    (q,r) = f `polyDivMod` g

prop_polyGCD_divisible =
  forAll upolynomials $ \a ->
  forAll upolynomials $ \b ->
    (a /= 0 && b /= 0) ==>
      let c = polyGCD a b
      in a `polyMod` c == 0 && b `polyMod` c == 0

prop_polyGCD_comm = 
  forAll upolynomials $ \a ->
  forAll upolynomials $ \b ->
    polyGCD a b == polyGCD b a

prop_polyGCD_euclid =
  forAll upolynomials $ \p ->
  forAll upolynomials $ \q ->
  forAll upolynomials $ \r ->
    (p /= 0 && q /= 0 && r /= 0) ==>
      polyGCD p q == polyGCD p (q + p*r)

case_polyGCD_1 = polyGCD f1 f2 @?= 1
  where 
    x :: UPolynomial Rational
    x = var X
    f1 = x^3 + x^2 + x
    f2 = x^2 + 1

eqUpToInvElem :: UPolynomial Integer -> UPolynomial Integer -> Bool
eqUpToInvElem 0 0 = True
eqUpToInvElem _ 0 = False
eqUpToInvElem a b =
  case mapCoeff fromInteger a `polyDivMod` mapCoeff fromInteger b of
    (q,r) -> r == 0 && deg q <= 0

prop_polyGCD'_comm = 
  forAll upolynomialsZ $ \a ->
  forAll upolynomialsZ $ \b ->
    polyGCD' a b `eqUpToInvElem` polyGCD' b a

prop_polyGCD'_euclid =
  forAll upolynomialsZ $ \p ->
  forAll upolynomialsZ $ \q ->
  forAll upolynomialsZ $ \r ->
    (p /= 0 && q /= 0 && r /= 0) ==>
      polyGCD' p q `eqUpToInvElem` polyGCD' p (q + p*r)

case_polyGCD'_1 = eqUpToInvElem (polyGCD' f1 f2) 1 @?= True
  where 
    x :: UPolynomial Integer
    x = var X
    f1 = x^3 + x^2 + x
    f2 = x^2 + 1

prop_polyLCM_divisible =
  forAll upolynomials $ \a ->
  forAll upolynomials $ \b ->
    (a /= 0 && b /= 0) ==>
      let c = polyLCM a b
      in c `polyMod` a == 0 && c `polyMod` b == 0

prop_polyLCM_comm = 
  forAll upolynomials $ \a ->
  forAll upolynomials $ \b ->
    polyLCM a b == polyLCM b a

prop_deriv_integral =
  forAll upolynomials $ \a ->
    deriv (integral a x) x == a
  where
    x = X

prop_integral_deriv =
  forAll upolynomials $ \a ->
    deg (integral (deriv a x) x - a) <= 0
  where
    x = X

prop_pp_cont =
  forAll polynomials $ \p ->
    cont (pp p) == 1

prop_cont_prod =
  forAll polynomials $ \p ->
    forAll polynomials $ \q ->
      (p /= 0 && q /= 0) ==>
        cont (p*q) == cont p * cont q

case_cont_pp_Integer = do
  cont p @?= 5
  pp p   @?= (-2*x^2 + x + 1)
  where
    x = var X
    p :: UPolynomial Integer
    p = -10*x^2 + 5*x + 5

case_cont_pp_Rational = do
  cont p @?= 1/6
  pp p   @?= (2*x^5 + 21*x^2 + 12*x + 6)
  where
    x = var X
    p :: UPolynomial Rational
    p = constant (1/3) * x^5 + constant (7/2) * x^2 + 2 * x + 1

{--------------------------------------------------------------------
  Monomial
--------------------------------------------------------------------}

{--------------------------------------------------------------------
  Monic Monomial
--------------------------------------------------------------------}

prop_degreeOfProduct =
  forAll monicMonomials $ \a -> 
  forAll monicMonomials $ \b -> 
    deg (a `mmProd` b) == deg a + deg b

prop_degreeOfOne =
  deg mmOne == 0

prop_mmProd_unitL = 
  forAll monicMonomials $ \a -> 
    mmOne `mmProd` a == a

prop_mmProd_unitR = 
  forAll monicMonomials $ \a -> 
    a `mmProd` mmOne == a

prop_mmProd_comm = 
  forAll monicMonomials $ \a -> 
  forAll monicMonomials $ \b -> 
    a `mmProd` b == b `mmProd` a

prop_mmProd_assoc = 
  forAll monicMonomials $ \a ->
  forAll monicMonomials $ \b ->
  forAll monicMonomials $ \c ->
    a `mmProd` (b `mmProd` c) == (a `mmProd` b) `mmProd` c

prop_mmProd_Divisible = 
  forAll monicMonomials $ \a -> 
  forAll monicMonomials $ \b -> 
    let c = a `mmProd` b
    in mmDivisible c a && mmDivisible c b

prop_mmProd_Div = 
  forAll monicMonomials $ \a -> 
  forAll monicMonomials $ \b -> 
    let c = a `mmProd` b
    in c `mmDiv` a == b && c `mmDiv` b == a

case_mmDeriv = mmDeriv p 1 @?= (2, q)
  where
    p = mmFromList [(1,2),(2,4)]
    q = mmFromList [(1,1),(2,4)]

-- lcm (x1^2 * x2^4) (x1^3 * x2^1) = x1^3 * x2^4
case_mmLCM = mmLCM p1 p2 @?= mmFromList [(1,3),(2,4)]
  where
    p1 = mmFromList [(1,2),(2,4)]
    p2 = mmFromList [(1,3),(2,1)]

-- gcd (x1^2 * x2^4) (x2^1 * x3^2) = x2
case_mmGCD = mmGCD p1 p2 @?= mmFromList [(2,1)]
  where
    p1 = mmFromList [(1,2),(2,4)]
    p2 = mmFromList [(2,1),(3,2)]

prop_mmLCM_divisible = 
  forAll monicMonomials $ \a -> 
  forAll monicMonomials $ \b -> 
    let c = mmLCM a b
    in c `mmDivisible` a && c `mmDivisible` b

prop_mmGCD_divisible = 
  forAll monicMonomials $ \a -> 
  forAll monicMonomials $ \b -> 
    let c = mmGCD a b
    in a `mmDivisible` c && b `mmDivisible` c

{--------------------------------------------------------------------
  Monomial Order
--------------------------------------------------------------------}

-- http://en.wikipedia.org/wiki/Monomial_order
case_lex = sortBy lex [a,b,c,d] @?= [b,a,d,c]
  where
    x = 1
    y = 2
    z = 3
    a = mmFromList [(x,1),(y,2),(z,1)]
    b = mmFromList [(z,2)]
    c = mmFromList [(x,3)]
    d = mmFromList [(x,2),(z,2)]

-- http://en.wikipedia.org/wiki/Monomial_order
case_grlex = sortBy grlex [a,b,c,d] @?= [b,c,a,d]
  where
    x = 1
    y = 2
    z = 3
    a = mmFromList [(x,1),(y,2),(z,1)]
    b = mmFromList [(z,2)]
    c = mmFromList [(x,3)]
    d = mmFromList [(x,2),(z,2)]

-- http://en.wikipedia.org/wiki/Monomial_order
case_grevlex = sortBy grevlex [a,b,c,d] @?= [b,c,d,a]
  where
    x = 1
    y = 2
    z = 3
    a = mmFromList [(x,1),(y,2),(z,1)]
    b = mmFromList [(z,2)]
    c = mmFromList [(x,3)]
    d = mmFromList [(x,2),(z,2)]

prop_refl_lex     = propRefl lex
prop_refl_grlex   = propRefl grlex
prop_refl_grevlex = propRefl grevlex

prop_trans_lex     = propTrans lex
prop_trans_grlex   = propTrans grlex
prop_trans_grevlex = propTrans grevlex

prop_sym_lex     = propSym lex
prop_sym_grlex   = propSym grlex
prop_sym_grevlex = propSym grevlex

prop_monomial_order_property1_lex     = monomialOrderProp1 lex
prop_monomial_order_property1_grlex   = monomialOrderProp1 grlex
prop_monomial_order_property1_grevlex = monomialOrderProp1 grevlex

prop_monomial_order_property2_lex     = monomialOrderProp2 lex
prop_monomial_order_property2_grlex   = monomialOrderProp2 grlex
prop_monomial_order_property2_grevlex = monomialOrderProp2 grevlex

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
           cmp (a `mmProd` c) (b `mmProd` c) == r

monomialOrderProp2 cmp =
  forAll monicMonomials $ \a ->
    a /= mmOne ==> cmp mmOne a == LT

{--------------------------------------------------------------------
  Gröbner basis
--------------------------------------------------------------------}

-- http://math.rice.edu/~cbruun/vigre/vigreHW6.pdf
-- Example 1
case_spolynomial = GB.spolynomial grlex f g @?= - x^3*y^3 - constant (1/3) * y^3 + x^2
  where
    x = var 1
    y = var 2
    f, g :: Polynomial Rational Int
    f = x^3*y^2 - x^2*y^3 + x
    g = 3*x^4*y + y^2


-- http://math.rice.edu/~cbruun/vigre/vigreHW6.pdf
-- Exercise 1
case_buchberger1 = Set.fromList gb @?= Set.fromList expected
  where
    gb = GB.basis lex [x^2-y, x^3-z]
    expected = [y^3 - z^2, x^2 - y, x*z - y^2, x*y - z]

    x :: Polynomial Rational Int
    x = var 1
    y = var 2
    z = var 3

-- http://math.rice.edu/~cbruun/vigre/vigreHW6.pdf
-- Exercise 2
case_buchberger2 = Set.fromList gb @?= Set.fromList expected
  where
    gb = GB.basis grlex [x^3-2*x*y, x^2*y-2*y^2+x]
    expected = [x^2, x*y, y^2 - constant (1/2) * x]

    x :: Polynomial Rational Int
    x = var 1
    y = var 2

-- http://www.iisdavinci.it/jeometry/buchberger.html
case_buchberger3 = Set.fromList gb @?= Set.fromList expected
  where
    gb = GB.basis lex [x^2+2*x*y^2, x*y+2*y^3-1]
    expected = [x, y^3 - constant (1/2)]
    x :: Polynomial Rational Int
    x = var 1
    y = var 2

-- http://www.orcca.on.ca/~reid/NewWeb/DetResDes/node4.html
-- 時間がかかるので自動実行されるテストケースには含めていない
disabled_case_buchberger4 = Set.fromList gb @?= Set.fromList expected                   
  where
    x :: Polynomial Rational Int
    x = var 1
    y = var 2
    z = var 3

    gb = GB.basis lex [x^2+y*z-2, x*z+y^2-3, x*y+z^2-5]

    expected = GB.reduceGBasis lex $
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
case_Seven_Trees_in_One = reduce lex (x^7 - x) gb @?= 0
  where
    x :: Polynomial Rational Int
    x = var 1
    gb = GB.basis lex [x-(x^2 + 1)]

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
  reduce lex (x^2 - y^2) gb @?= 0
  where
    x :: Polynomial Rational Int
    x = var 1
    y = var 2
    z = var 3
    f = x^2 - y
    g = y - z
    h = x + z
    f' = z^2 - z
    gb = GB.basis lex [f, g, h]

{--------------------------------------------------------------------
  Generators
--------------------------------------------------------------------}

monicMonomials :: Gen (MonicMonomial Int)
monicMonomials = do
  size <- choose (0, 3)
  xs <- replicateM size $ do
    v <- choose (-5, 5)
    e <- liftM ((+1) . abs) arbitrary
    return $ mmFromList [(v,e)]
  return $ foldl mmProd mmOne xs

monomials :: Gen (Monomial Rational Int)
monomials = do
  m <- monicMonomials
  c <- arbitrary
  return (c,m)

polynomials :: Gen (Polynomial Rational Int)
polynomials = do
  size <- choose (0, 5)
  xs <- replicateM size monomials
  return $ sum $ map fromMonomial xs 

umonicMonomials :: Gen (MonicMonomial X)
umonicMonomials = do
  size <- choose (0, 3)
  xs <- replicateM size $ do
    e <- choose (1, 4)
    return $ mmFromList [(X,e)]
  return $ foldl mmProd mmOne xs

umonomials :: Gen (Monomial Rational X)
umonomials = do
  m <- umonicMonomials
  c <- arbitrary
  return (c,m)

upolynomials :: Gen (UPolynomial Rational)
upolynomials = do
  size <- choose (0, 5)
  xs <- replicateM size umonomials
  return $ sum $ map fromMonomial xs 

umonomialsZ :: Gen (Monomial Integer X)
umonomialsZ = do
  m <- umonicMonomials
  c <- arbitrary
  return (c,m)

upolynomialsZ :: Gen (UPolynomial Integer)
upolynomialsZ = do
  size <- choose (0, 5)
  xs <- replicateM size umonomialsZ
  return $ sum $ map fromMonomial xs 

------------------------------------------------------------------------

-- http://mathworld.wolfram.com/SturmFunction.html
case_sturmChain = sturmChain p0 @?= chain
  where
    x = var X
    p0 = x^5 - 3*x - 1
    p1 = 5*x^4 - 3
    p2 = constant (1/5) * (12*x + 5)
    p3 = constant (59083 / 20736)
    chain = [p0, p1, p2, p3]

-- http://mathworld.wolfram.com/SturmFunction.html
case_numRoots_1 =
  sequence_
  [ numRoots p (Finite (-2)   <=..<= Finite 0)      @?= 2
  , numRoots p (Finite 0      <=..<= Finite 2)      @?= 1
  , numRoots p (Finite (-1.5) <=..<= Finite (-1.0)) @?= 1
  , numRoots p (Finite (-0.5) <=..<= Finite 0)      @?= 1
  , numRoots p (Finite 1      <=..<= Finite (1.5))  @?= 1
  ]
  where
    x = var X
    p = x^5 - 3*x - 1

-- check interpretation of intervals
case_numRoots_2 =
  sequence_
  [ numRoots p (Finite 2 <..<=  Finite 3) @?= 0
  , numRoots p (Finite 2 <=..<= Finite 3) @?= 1
  , numRoots p (Finite 1 <..<   Finite 2) @?= 0
  , numRoots p (Finite 1 <..<=  Finite 2) @?= 1
  ]
  where
    x = var X
    p = x^2 - 4

case_separate = do
  forM_ (zip vals intervals) $ \(v,ival) -> do
    Interval.member v ival @?= True
    forM_ (filter (v/=) vals) $ \v2 -> do
      Interval.member v2 ival @?= False
  where
    x = var X
    p = x^5 - 3*x - 1
    intervals = separate p
    vals = [-1.21465, -0.334734, 1.38879]

------------------------------------------------------------------------

case_factorZ_zero = FactorZ.factor 0 @?= [0]
case_factorZ_one  = FactorZ.factor 1 @?= []
case_factorZ_two  = FactorZ.factor 2 @?= [2]

-- http://en.wikipedia.org/wiki/Factorization_of_polynomials
case_factorZ_test1 = do
  sort (FactorZ.factor f) @?= sort [2,p,q]
  product (FactorZ.factor f) @?= f
  where
    x :: UPolynomial Integer
    x = var X   
    f = 2*(x^5 + x^4 + x^2 + x + 2)
    p = x^2 + x + 1
    q = x^3 - x + 2

case_factorZ_test2 = do
  sort (FactorZ.factor f) @?= sort [-1,p,q]
  product (FactorZ.factor f) @?= f
  where
    x :: UPolynomial Integer
    x = var X   
    f = - (x^5 + x^4 + x^2 + x + 2)
    p = x^2 + x + 1
    q = x^3 - x + 2

case_factorQ_zero = FactorQ.factor 0 @?= [0]
case_factorQ_one  = FactorQ.factor 1 @?= []
case_factorQ_two  = FactorQ.factor 2 @?= [2]

-- http://en.wikipedia.org/wiki/Factorization_of_polynomials
case_factorQ_test1 = do
  sort (FactorQ.factor f) @?= sort [2,p,q]
  product (FactorQ.factor f) @?= f
  where
    x :: UPolynomial Rational
    x = var X
    f = 2*(x^5 + x^4 + x^2 + x + 2)
    p = x^2 + x + 1
    q = x^3 - x + 2

case_factorQ_test2 = do
  sort (FactorQ.factor f) @?= sort [-1,p,q]
  product (FactorQ.factor f) @?= f
  where
    x :: UPolynomial Rational
    x = var X
    f = - (x^5 + x^4 + x^2 + x + 2)
    p = x^2 + x + 1
    q = x^3 - x + 2

-- http://en.wikipedia.org/wiki/Factorization_of_polynomials_over_a_finite_field_and_irreducibility_tests
case_FF_sqfree_test1 = do
  sort actual @?= sort expected
  product [f^n | (f,n) <- actual] @?= f
  where
    x :: UPolynomial $(FF.primeField 3)
    x = var X
    f  = x^11 + 2*x^9 + 2*x^8 + x^6 + x^5 + 2*x^3 + 2*x^2 + 1
    actual   = FactorFF.sqfree f
    expected = [(x+1, 1), (x^2+1, 3), (x+2, 4)]

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
    x = var X
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
    x = var X
    f = 1 - x^100
    actual   = FactorFF.factor f
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
    x = var X
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
--     x = var X
--     f = 2 + x + x^2 + x^3 + x^4 + x^5
--     actual   = FactorFF.berlekamp f
--     expected = [1*x+13077, 1*x^4+18915*x^3+2958*x^2+27345*x+4834]

------------------------------------------------------------------------

-- http://en.wikipedia.org/wiki/Lagrange_polynomial
case_Lagrange_interpolation_1 = p @?= q
  where
    x :: UPolynomial Rational
    x = var X
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
    x = var X
    p = LagrangeInterpolation.interpolate
        [ (1, 1)
        , (2, 8)
        , (3, 27)
        ]
    q = 6*x^2 - 11*x + 6

------------------------------------------------------------------------
-- Test harness

main :: IO ()
main = $(defaultMainGenerator)
