-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.AlgebraicNumber.Complex
-- Copyright   :  (c) Masahiro Sakai 2013
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Algebraic Numbers
--
-----------------------------------------------------------------------------
module ToySolver.Data.AlgebraicNumber.Complex
    (
    -- * Rectangular form
      AComplex((:+))

    -- * Properties
    , realPart          -- :: AComplex -> AReal
    , imagPart          -- :: AComplex -> AReal
    , magnitude         -- :: AComplex -> AReal
    , minimalPolynomial -- :: AComplex -> UPolynomial Rational

    -- * Operations
    , conjugate         -- :: AComplex -> AComplex
    ) where

import Control.Monad
import qualified Data.Sign as Sign
import qualified Data.Map as Map
import Data.Maybe

import qualified ToySolver.Arith.CAD as CAD
import qualified ToySolver.Data.AlgebraicNumber.Real as AReal
import ToySolver.Data.AlgebraicNumber.Real (AReal)
import qualified ToySolver.Data.AlgebraicNumber.Root as Root
import qualified ToySolver.Data.Polynomial as P
import ToySolver.Data.Polynomial (Polynomial, UPolynomial, X (..))

infix  6  :+

-- -----------------------------------------------------------------------------
-- The Complex type

-- | Complex numbers are an algebraic type.
--
-- For a complex number @z@, @'abs' z@ is a number with the magnitude of @z@,
-- but oriented in the positive real direction, whereas @'signum' z@
-- has the phase of @z@, but unit magnitude.
data AComplex = !AReal :+ !AReal
    deriving (Eq, Show)

-- -----------------------------------------------------------------------------
-- Functions over Complex

-- | Extracts the real part of a complex number.
realPart :: AComplex -> AReal
realPart (x :+ _) = x

-- | Extracts the imaginary part of a complex number.
imagPart :: AComplex -> AReal
imagPart (_ :+ y) = y

-- | The conjugate of a complex number.
conjugate :: AComplex -> AComplex
conjugate (x :+ y) =  x :+ (-y)

-- | The nonnegative magnitude of a complex number.
magnitude :: AComplex -> AReal
magnitude (x :+ y) = AReal.nthRoot 2 (x*x + y*y)

-- -----------------------------------------------------------------------------
-- Instances of Complex

instance  Num AComplex where
    (x:+y) + (x':+y')   =  (x+x') :+ (y+y')
    (x:+y) - (x':+y')   =  (x-x') :+ (y-y')
    (x:+y) * (x':+y')   =  (x*x'-y*y') :+ (x*y'+y*x')
    negate (x:+y)       =  negate x :+ negate y
    abs z               =  magnitude z :+ 0
    signum (0:+0)       =  0
    signum z@(x:+y)     =  x/r :+ y/r  where r = magnitude z
    fromInteger n       =  fromInteger n :+ 0

instance  Fractional AComplex  where
    (x:+y) / (x':+y')   =  (x*x'+y*y') / d :+ (y*x'-x*y') / d
                           where d   = x'*x' + y'*y'
    fromRational a      =  fromRational a :+ 0

-- -----------------------------------------------------------------------------

-- | The polynomial of which the algebraic number is root.
minimalPolynomial :: AComplex -> UPolynomial Rational
minimalPolynomial z@(x :+ y) =
  head [q | (q,_) <- P.factor p, P.deg q > 0, P.eval (\X -> z) (P.mapCoeff fromRational q) == 0]
  where
    p = Root.findPoly (P.var a + P.var b * P.var i) ps
      where
        a, b, i :: Int
        i = 0
        a = 1
        b = 2
        ps =
          [ (P.var i) ^ 2 + 1
          , P.subst (AReal.minimalPolynomial x) (\X -> P.var a)
          , P.subst (AReal.minimalPolynomial y) (\X -> P.var b)
          ]

-- -----------------------------------------------------------------------------

-- | Roots of the polynomial
roots :: UPolynomial Rational -> [AComplex]
roots f = do
  let cs1 = [ (u, [Sign.Zero]), (v, [Sign.Zero]) ]
  (cs2, cells2) <- CAD.project' [(P.toUPolynomialOf p 0, ss) | (p,ss) <- cs1]
  (cs3, cells3) <- CAD.project' [(P.toUPolynomialOf p 1, ss) | (p,ss) <- cs2]
  guard $ and [Sign.signOf v `elem` ss | (p,ss) <- cs3, let v = P.eval (\_ -> undefined) p]

  let m3 = Map.empty
  yval <- catMaybes [CAD.findSample m3 cell | cell <- cells3]
  let m2 = Map.insert 1 yval m3
  xval <- catMaybes [CAD.findSample m2 cell | cell <- cells2]

  return $ xval :+ yval

  where

    -- f(x + yi) = u(x,y) + v(x,y)i
    f1 :: P.Polynomial Rational Int
    f1 = P.subst f (\X -> P.var 0 + P.var 1 * P.var 2)
    f2 = P.toUPolynomialOf (P.reduce P.grevlex f1 [P.var 2 * P.var 2 + 1]) 2
    u = P.coeff P.mone f2
    v = P.coeff (P.var X) f2

-- -----------------------------------------------------------------------------

test1 = minimalPolynomial (sqrt2 :+ sqrt3)
  where
    sqrt2 = AReal.nthRoot 2 2
    sqrt3 = AReal.nthRoot 2 3

test2 = magnitude (sqrt2 :+ sqrt3)
  where
    sqrt2 = AReal.nthRoot 2 2
    sqrt3 = AReal.nthRoot 2 3

test3 = roots p
  where
    x = P.var X
    p = x - 2

test4 = roots p
  where
    x = P.var X
    p = x^2 - 2

test5 = roots p
  where
    x = P.var X
    p = x^3 - 1

test6 = roots p
  where
    x = P.var X
    p = x^4 + 2*x^2 + 25
