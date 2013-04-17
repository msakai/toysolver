{-# LANGUAGE Rank2Types #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.AlgebraicNumber.Real
-- Copyright   :  (c) Masahiro Sakai 2012-2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (Rank2Types)
--
-- Algebraic reals
--
-- Reference:
--
-- * Why the concept of a field extension is a natural one
--   <http://www.dpmms.cam.ac.uk/~wtg10/galois.html>
-- 
-----------------------------------------------------------------------------
module Data.AlgebraicNumber.Real
  (
  -- * Algebraic real type
    AReal

  -- * Construction
  , realRoots

  -- * Properties
  , minimalPolynomial
  , deg
  , isRational
  , isAlgebraicInteger
  , height

  -- * Approximation
  , approx

  -- * Misc
  , simpARealPoly
  , goldenRatio
  ) where

import Control.Exception (assert)
import Control.Monad
import Data.List
import Data.Ratio
import qualified Text.PrettyPrint.HughesPJClass as PP
import Text.PrettyPrint.HughesPJClass (Doc, PrettyLevel, Pretty (..), prettyParen)

import Data.Polynomial hiding (deg)
import qualified Data.Polynomial as P
import qualified Data.Polynomial.Factorization.Rational as FactorQ
import qualified Data.Polynomial.RootSeparation.Sturm as Sturm
import Data.Interval (Interval, EndPoint (..), (<=..<), (<..<=), (<..<), (<!), (>!))
import qualified Data.Interval as Interval
import Data.AlgebraicNumber.Root

{--------------------------------------------------------------------
  Construction
--------------------------------------------------------------------}

-- | Algebraic real numbers.
data AReal = RealRoot (UPolynomial Rational) (Interval Rational)
  deriving Show

-- | Real roots of the polynomial in ascending order.
realRoots :: UPolynomial Rational -> [AReal]
realRoots p = sort $ do
  q <- FactorQ.factor p
  realRoots' q

-- p must already be factored.
realRoots' :: UPolynomial Rational -> [AReal]
realRoots' p = sort $ do
  guard $ P.deg p > 0
  i <- Sturm.separate p
  return $ realRoot' p i

realRoot :: UPolynomial Rational -> Interval Rational -> AReal
realRoot p i = 
  case [q | q <- FactorQ.factor p, P.deg q > 0, Sturm.numRoots q i == 1] of
    p2:_ -> realRoot' p2 i
    []   -> error "Data.AlgebraicNumber.Real.realRoot: invalid interval"

-- p must already be factored.
realRoot' :: UPolynomial Rational -> Interval Rational -> AReal
realRoot' p i = RealRoot (normalizePoly p) i

{--------------------------------------------------------------------
  Operations
--------------------------------------------------------------------}

isZero :: AReal -> Bool
isZero a = 0 `Interval.member` (interval a) && 0 `isRootOf` minimalPolynomial a

scaleAReal :: Rational -> AReal -> AReal
scaleAReal r a = realRoot' p2 i2
  where
    p2 = rootScale r (minimalPolynomial a)
    i2 = Interval.singleton r * interval a

shiftAReal :: Rational -> AReal -> AReal
shiftAReal r a = realRoot' p2 i2
  where
    p2 = rootShift r (minimalPolynomial a)
    i2 = Interval.singleton r + interval a

instance Eq AReal where
  a == b = p1==p2 && Sturm.numRoots' c (Interval.intersection i1 i2) == 1
    where
      p1 = minimalPolynomial a
      p2 = minimalPolynomial b
      i1 = interval a
      i2 = interval b
      c  = sturmChain a

instance Ord AReal where
  compare a b
    | i1 >! i2  = GT
    | i1 <! i2  = LT
    | a == b    = EQ
    | otherwise = go i1 i2
    where
      i1 = interval a
      i2 = interval b
      c1 = sturmChain a
      c2 = sturmChain b
      go i1 i2
        | i1 >! i2 = GT
        | i1 <! i2 = LT
        | otherwise =
            if w1 > w2
            then go (Sturm.narrow' c1 i1 (w1 / 2)) i2
            else go i1 (Sturm.narrow' c2 i2 (w2 / 2))
        where
          w1 = Interval.width i1
          w2 = Interval.width i2

instance Num AReal where
  a + b
    | isRational a = shiftAReal (toRational a) b
    | isRational b = shiftAReal (toRational b) a
    | otherwise    = realRoot p3 i3
    where
      p3 = rootAdd (minimalPolynomial a) (minimalPolynomial b)
      c1 = sturmChain a
      c2 = sturmChain b
      c3 = Sturm.sturmChain p3
      i3 = go (interval a) (interval b) (Sturm.separate' c3)

      go i1 i2 is3 =
        case [i5 | i3 <- is3, let i5 = Interval.intersection i3 i4, Sturm.numRoots' c3 i5 > 0] of
          [] -> error "AReal.+: should not happen"
          [i5] -> i5
          is5 ->
            go (Sturm.narrow' c1 i1 (Interval.width i1 / 2))
               (Sturm.narrow' c2 i2 (Interval.width i2 / 2))
               [Sturm.narrow' c3 i5 (Interval.width i5 / 2) | i5 <- is5]
        where
          i4 = i1 + i2

  a * b
    | isRational a = scaleAReal (toRational a) b
    | isRational b = scaleAReal (toRational b) a
    | otherwise    = realRoot p3 i3
    where
      p3 = rootMul (minimalPolynomial a) (minimalPolynomial b)
      c1 = sturmChain a
      c2 = sturmChain b
      c3 = Sturm.sturmChain p3
      i3 = go (interval a) (interval b) (Sturm.separate' c3)

      go i1 i2 is3 =
        case [i5 | i3 <- is3, let i5 = Interval.intersection i3 i4, Sturm.numRoots' c3 i5 > 0] of
          [] -> error "AReal.*: should not happen"
          [i5] -> i5
          is5 ->
            go (Sturm.narrow' c1 i1 (Interval.width i1 / 2))
               (Sturm.narrow' c2 i2 (Interval.width i2 / 2))
               [Sturm.narrow' c3 i5 (Interval.width i5 / 2) | i5 <- is5]
        where
          i4 = i1 * i2

  negate a = scaleAReal (-1) a

  abs a =
    case compare 0 a of
      EQ -> fromInteger 0
      LT -> a
      GT -> negate a

  signum a = fromInteger $
    case compare 0 a of
      EQ -> 0
      LT -> 1
      GT -> -1

  fromInteger = fromRational . toRational

instance Fractional AReal where
  fromRational r = realRoot' (x - constant r) (Interval.singleton r)
    where
      x = var X

  recip a
    | isZero a  = error "AReal.recip: zero division"
    | otherwise = realRoot' p2 i2
      where
        p2 = rootRecip (minimalPolynomial a)
        i2 = recip (interval a)

instance Real AReal where
  toRational x
    | isRational x =
        let p = minimalPolynomial x
            a = P.coeff (P.mmVar X) p
            b = P.coeff P.mmOne p
        in - b / a
    | otherwise  = error "toRational: proper algebraic number"

instance RealFrac AReal where
  properFraction = properFraction'
  truncate       = truncate'
  round          = round'
  ceiling        = ceiling'
  floor          = floor'

-- | Returns approximate rational value such that @abs (a - approx a epsilon) <= epsilon@.
approx
  :: AReal    -- ^ a
  -> Rational -- ^ epsilon
  -> Rational
approx a epsilon =
  if isRational a
    then toRational a
    else Sturm.approx' (sturmChain a) (interval a) epsilon

-- | Same as 'properFraction'.
properFraction' :: Integral b => AReal -> (b, AReal)
properFraction' x =
  case compare x 0 of
    EQ -> (0, 0)
    GT -> (fromInteger floor_x, x - fromInteger floor_x)
    LT -> (fromInteger ceiling_x, x - fromInteger ceiling_x)
  where
    floor_x   = floor' x
    ceiling_x = ceiling' x

-- | Same as 'truncate'.
truncate' :: Integral b => AReal -> b
truncate' = fst . properFraction'

-- | Same as 'round'.
round' :: Integral b => AReal -> b
round' x = 
  case signum (abs r - 0.5) of
    -1 -> n
    0  -> if even n then n else m
    1  -> m
    _  -> error "round default defn: Bad value"
  where
    (n,r) = properFraction' x
    m = if r < 0 then n - 1 else n + 1

-- | Same as 'ceiling'.
ceiling' :: Integral b => AReal -> b
ceiling' a =
  if Sturm.numRoots' chain (Interval.intersection i2 i3) >= 1
    then fromInteger ceiling_lb
    else fromInteger ceiling_ub
  where
    chain = sturmChain a
    i2 = Sturm.narrow' chain (interval a) (1/2)
    (Finite lb, inLB) = Interval.lowerBound' i2
    (Finite ub, inUB) = Interval.upperBound' i2
    ceiling_lb = ceiling lb
    ceiling_ub = ceiling ub
    i3 = NegInf <..<= Finite (fromInteger ceiling_lb)

-- | Same as 'floor'.
floor' :: Integral b => AReal -> b
floor' a =
  if Sturm.numRoots' chain (Interval.intersection i2 i3) >= 1
    then fromInteger floor_ub
    else fromInteger floor_lb
  where
    chain = sturmChain a
    i2 = Sturm.narrow' chain (interval a) (1/2)
    (Finite lb, inLB) = Interval.lowerBound' i2
    (Finite ub, inUB) = Interval.upperBound' i2
    floor_lb = floor lb
    floor_ub = floor ub
    i3 = Finite (fromInteger floor_ub) <=..< PosInf

{--------------------------------------------------------------------
  Properties
--------------------------------------------------------------------}

-- | The polynomial of which the algebraic number is root.
minimalPolynomial :: AReal -> UPolynomial Rational
minimalPolynomial (RealRoot p _) = p

sturmChain :: AReal -> Sturm.SturmChain
sturmChain a = Sturm.sturmChain (minimalPolynomial a)

interval :: AReal -> Interval Rational
interval (RealRoot _ i) = i

-- | Degree of the algebraic number.
-- 
-- If the algebraic number's 'minimalPolynomial' has degree @n@,
-- then the algebraic number is said to be degree @n@.
deg :: AReal -> Integer
deg a = P.deg $ minimalPolynomial a

-- | Whether the algebraic number is a rational.
isRational :: AReal -> Bool
isRational x = deg x == 1

-- | Whether the algebraic number is a root of a polynomial with integer
-- coefficients with leading coefficient @1@ (a monic polynomial).
isAlgebraicInteger :: AReal -> Bool
isAlgebraicInteger x = cn * fromIntegral d == 1
  where
    p = minimalPolynomial x
    d = foldl' lcm 1 [denominator c | (c,_) <- terms p]
    (cn,_) = leadingTerm grlex p

-- | Height of the algebraic number.
height :: AReal -> Integer
height x = maximum [ assert (denominator c' == 1) (abs (numerator c'))
                   | (c,_) <- terms p, let c' = c * fromInteger d ]
  where
    p = minimalPolynomial x
    d = foldl' lcm 1 [denominator c | (c,_) <- terms p]

{--------------------------------------------------------------------
  Pretty printing
--------------------------------------------------------------------}

instance Pretty AReal where
  pPrintPrec lv prec r =
    prettyParen (prec > appPrec) $
      PP.hsep [PP.text "RealRoot", pPrintPrec lv (appPrec+1) p, PP.int idx]
    where
      p = minimalPolynomial r
      Just idx = r `elemIndex`  sort (realRoots' p)
      appPrec = 10

instance PrettyCoeff AReal where
  pPrintCoeff = pPrintPrec
  isNegativeCoeff = (0>)

{--------------------------------------------------------------------
  Manipulation of polynomials
--------------------------------------------------------------------}

-- 代数的数を係数とする多項式の根を、有理数係数多項式の根として表す
simpARealPoly :: UPolynomial AReal -> UPolynomial Rational
simpARealPoly p = rootSimpPoly minimalPolynomial p

{--------------------------------------------------------------------
  Misc
--------------------------------------------------------------------}

-- | Golden ratio 
goldenRatio :: AReal
goldenRatio = (1 + root5) / 2
  where
    [_, root5] = sort $ realRoots' ((var X)^2 - 5)
