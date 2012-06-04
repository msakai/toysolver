{-# LANGUAGE TemplateHaskell #-}

import Prelude hiding (lex)
import Data.List
import Data.Ratio
import qualified Data.Set as Set
import qualified Data.IntMultiSet as IMS
import Test.HUnit hiding (Test)
import Test.Framework (Test, defaultMain, testGroup)
import Test.Framework.TH
import Test.Framework.Providers.HUnit
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
-- lexでやりたいけど、lexだとしばらく待っても終わらなかった
test_buchberger4 = buchberger grlex [x^2+y*z-2, x*z+y^2-3, x*y+z^2-5]
  where
    x :: Polynomial Rational
    x = var 1
    y = var 2
    z = var 3

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
