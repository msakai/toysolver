{-# LANGUAGE TemplateHaskell #-}

import Prelude hiding (lex)
import Control.Monad
import Data.List
import Data.Ratio
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.IntMultiSet as IMS
import Test.HUnit hiding (Test)
import Test.QuickCheck
import Test.Framework (Test, defaultMain, testGroup)
import Test.Framework.TH
import Test.Framework.Providers.HUnit
import Test.Framework.Providers.QuickCheck2
import Polynomial

-- http://en.wikipedia.org/wiki/Monomial_order
case_lex = sortBy lex [a,b,c,d] @?= [b,a,d,c]
  where
    x = 1
    y = 2
    z = 3
    a = IMS.fromOccurList [(x,1),(y,2),(z,1)]
    b = IMS.fromOccurList [(z,2)]
    c = IMS.fromOccurList [(x,3)]
    d = IMS.fromOccurList [(x,2),(z,2)]

-- http://en.wikipedia.org/wiki/Monomial_order
case_grlex = sortBy grlex [a,b,c,d] @?= [b,c,a,d]
  where
    x = 1
    y = 2
    z = 3
    a = IMS.fromOccurList [(x,1),(y,2),(z,1)]
    b = IMS.fromOccurList [(z,2)]
    c = IMS.fromOccurList [(x,3)]
    d = IMS.fromOccurList [(x,2),(z,2)]

-- http://en.wikipedia.org/wiki/Monomial_order
case_grevlex = sortBy grevlex [a,b,c,d] @?= [b,c,d,a]
  where
    x = 1
    y = 2
    z = 3
    a = IMS.fromOccurList [(x,1),(y,2),(z,1)]
    b = IMS.fromOccurList [(z,2)]
    c = IMS.fromOccurList [(x,3)]
    d = IMS.fromOccurList [(x,2),(z,2)]

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
           cmp (IMS.union a c) (IMS.union b c) == r

monomialOrderProp2 cmp =
  forAll monicMonomials $ \a ->
    a /= IMS.empty ==> cmp IMS.empty a == LT

monicMonomials = do
  size <- choose (0, 3)
  liftM (IMS.unions) $ replicateM size $ do
    v <- choose (-5, 5)
    e <- choose (1,100) -- liftM ((+1) . abs) arbitrary -- e should be >0
    return $ IMS.fromOccurList [(v,e)]
-- IntMultiSetを使ってるとIntのオーバーフローですぐダメになるなぁ。

-- http://math.rice.edu/~cbruun/vigre/vigreHW6.pdf
-- Example 1
case_spolynomial = spolynomial grlex f g @?= - x^3*y^3 - constant (1/3) * y^3 + x^2
  where
    x = var 1
    y = var 2
    f, g :: Polynomial Rational
    f = x^3*y^2 - x^2*y^3 + x
    g = 3*x^4*y + y^2


-- http://math.rice.edu/~cbruun/vigre/vigreHW6.pdf
-- Exercise 1
case_buchberger1 = Set.fromList gbase @?= Set.fromList expected
  where
    gbase = buchberger lex [x^2-y, x^3-z]
    expected = [y^3 - z^2, x^2 - y, x*z - y^2, x*y - z]

    x :: Polynomial Rational
    x = var 1
    y = var 2
    z = var 3

-- http://math.rice.edu/~cbruun/vigre/vigreHW6.pdf
-- Exercise 2
case_buchberger2 = Set.fromList gbase @?= Set.fromList expected
  where
    gbase = buchberger grlex [x^3-2*x*y, x^2*y-2*y^2+x]
    expected = [x^2, x*y, y^2 - constant (1/2) * x]

    x :: Polynomial Rational
    x = var 1
    y = var 2

-- http://www.iisdavinci.it/jeometry/buchberger.html
case_buchberger3 = Set.fromList gbase @?= Set.fromList expected
  where
    gbase = buchberger lex [x^2+2*x*y^2, x*y+2*y^3-1]
    expected = [x, y^3 - constant (1/2)]
    x :: Polynomial Rational
    x = var 1
    y = var 2

-- http://www.orcca.on.ca/~reid/NewWeb/DetResDes/node4.html
-- 時間がかかるので自動実行されるテストケースには含めていない
test_buchberger4 = Set.fromList gbase @?= Set.fromList expected                   
  where
    x :: Polynomial Rational
    x = var 1
    y = var 2
    z = var 3

    gbase = buchberger lex [x^2+y*z-2, x*z+y^2-3, x*y+z^2-5]

    expected = reduceGBase lex $
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
case_Seven_Trees_in_One = reduce lex (x^7 - x) gbase @?= 0
  where
    x :: Polynomial Rational
    x = var 1
    gbase = buchberger lex [x-(x^2 + 1)]

-- Non-linear loop invariant generation using Gröbner bases
-- http://portal.acm.org/citation.cfm?id=964028
-- http://www-step.stanford.edu/papers/popl04.pdf
-- Example 3
-- Consider again the ideal from Example 2; I = {f : x^2-y, g : y-z, h
-- : x+z}.  The Gröbner basis for I is G = {f' : z^2-z, g : y-z, h :
-- x+z}. With this basis, every reduction of p : x^2 - y^2 will yield
-- a normal form 0.
case_sankaranarayanan04nonlinear = do
  Set.fromList gbase @?= Set.fromList [f', g, h]
  reduce lex (x^2 - y^2) gbase @?= 0
  where
    x :: Polynomial Rational
    x = var 1
    y = var 2
    z = var 3
    f = x^2 - y
    g = y - z
    h = x + z
    f' = z^2 - z
    gbase = buchberger lex [f, g, h]

------------------------------------------------------------------------
-- Test harness

main :: IO ()
main = $(defaultMainGenerator)
