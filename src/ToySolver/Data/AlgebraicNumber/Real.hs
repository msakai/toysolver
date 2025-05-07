{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE Rank2Types #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.AlgebraicNumber.Real
-- Copyright   :  (c) Masahiro Sakai 2012-2013
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- Algebraic reals
--
-- Reference:
--
-- * Why the concept of a field extension is a natural one
--   <http://www.dpmms.cam.ac.uk/~wtg10/galois.html>
--
-----------------------------------------------------------------------------
module ToySolver.Data.AlgebraicNumber.Real
  (
  -- * Algebraic real type
    AReal

  -- * Construction
  , realRoots
  , realRootsEx

  -- * Properties
  , minimalPolynomial
  , isolatingInterval
  , isRational
  , isAlgebraicInteger
  , height
  , rootIndex

  -- * Operations
  , nthRoot
  , refineIsolatingInterval

  -- * Approximation
  , approx
  , approxInterval

  -- * Misc
  , simpARealPoly
  , goldenRatio
  ) where

import Control.Exception (assert)
import Control.Monad
import Data.List (delete, elemIndex, sort)
import Data.Ratio
import qualified Data.Set as Set
import qualified Text.PrettyPrint.HughesPJClass as PP
import Text.PrettyPrint.HughesPJClass (Doc, PrettyLevel, Pretty (..), maybeParens)

import Data.Interval (Interval, Extended (..), (<=..<), (<..<=), (<..<), (<!), (>!))
import qualified Data.Interval as Interval

import ToySolver.Data.Polynomial (Polynomial, UPolynomial, X (..))
import qualified ToySolver.Data.Polynomial as P
import ToySolver.Data.AlgebraicNumber.Root
import qualified ToySolver.Data.AlgebraicNumber.Sturm as Sturm

{--------------------------------------------------------------------
  Construction
--------------------------------------------------------------------}

-- | Algebraic real numbers.
data AReal = RealRoot (UPolynomial Rational) (Interval Rational)
  deriving Show

-- | Real roots of the polynomial in ascending order.
realRoots :: UPolynomial Rational -> [AReal]
realRoots p = Set.toAscList $ Set.fromList $ do
  (q,_) <- P.factor p
  realRoots' q

-- | Real roots of the polynomial in ascending order.
realRootsEx :: UPolynomial AReal -> [AReal]
realRootsEx p
  | and [isRational c | (c,_) <- P.terms p] = realRoots $ P.mapCoeff toRational p
  | otherwise = [a | a <- realRoots (simpARealPoly p), a `P.isRootOf` p]

-- p must already be factored.
realRoots' :: UPolynomial Rational -> [AReal]
realRoots' p = do
  guard $ P.deg p > 0
  i <- Sturm.separate p
  return $ realRoot' p i

realRoot :: UPolynomial Rational -> Interval Rational -> AReal
realRoot p i =
  case [q | (q,_) <- P.factor p, P.deg q > 0, Sturm.numRoots q i == 1] of
    p2:_ -> realRoot' p2 i
    []   -> error "ToySolver.Data.AlgebraicNumber.Real.realRoot: invalid interval"

-- p must already be factored.
realRoot' :: UPolynomial Rational -> Interval Rational -> AReal
realRoot' p i = RealRoot (normalizePoly p) i

{--------------------------------------------------------------------
  Operations
--------------------------------------------------------------------}

isZero :: AReal -> Bool
isZero a = 0 `Interval.member` isolatingInterval a && 0 `P.isRootOf` minimalPolynomial a

scaleAReal :: Rational -> AReal -> AReal
scaleAReal r a = realRoot' p2 i2
  where
    p2 = rootScale r (minimalPolynomial a)
    i2 = Interval.singleton r * isolatingInterval a

shiftAReal :: Rational -> AReal -> AReal
shiftAReal r a = realRoot' p2 i2
  where
    p2 = rootShift r (minimalPolynomial a)
    i2 = Interval.singleton r + isolatingInterval a

instance Eq AReal where
  a == b = p1==p2 && Sturm.numRoots' c (Interval.intersection i1 i2) == 1
    where
      p1 = minimalPolynomial a
      p2 = minimalPolynomial b
      i1 = isolatingInterval a
      i2 = isolatingInterval b
      c  = sturmChain a

instance Ord AReal where
  compare a b
    | i1 >! i2  = GT
    | i1 <! i2  = LT
    | a == b    = EQ
    | otherwise = go i1 i2
    where
      i1 = isolatingInterval a
      i2 = isolatingInterval b
      c1 = sturmChain a
      c2 = sturmChain b
      go i1 i2
        | i1 >! i2 = GT
        | i1 <! i2 = LT
        | otherwise =
            if Interval.width i1 > Interval.width i2
            then go (Sturm.halve' c1 i1) i2
            else go i1 (Sturm.halve' c2 i2)

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
      i3 = go (isolatingInterval a) (isolatingInterval b) (Sturm.separate' c3)

      go i1 i2 is3 =
        case [i5 | i3 <- is3, let i5 = Interval.intersection i3 i4, Sturm.numRoots' c3 i5 > 0] of
          []   -> error "AReal.+: should not happen"
          [i5] -> i5
          is5  -> go (Sturm.halve' c1 i1) (Sturm.halve' c2 i2) [Sturm.halve' c3 i5 | i5 <- is5]
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
      i3 = go (isolatingInterval a) (isolatingInterval b) (Sturm.separate' c3)

      go i1 i2 is3 =
        case [i5 | i3 <- is3, let i5 = Interval.intersection i3 i4, Sturm.numRoots' c3 i5 > 0] of
          []   -> error "AReal.*: should not happen"
          [i5] -> i5
          is5  -> go (Sturm.halve' c1 i1) (Sturm.halve' c2 i2) [Sturm.halve' c3 i5 | i5 <- is5]
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
  fromRational r = realRoot' (x - P.constant r) (Interval.singleton r)
    where
      x = P.var X

  recip a
    | isZero a  = error "AReal.recip: zero division"
    | otherwise = realRoot' p2 i2
      where
        p2 = rootRecip (minimalPolynomial a)
        c1 = sturmChain a
        c2 = Sturm.sturmChain p2
        i2 = go (isolatingInterval a) (Sturm.separate' c2)
        go i1 is2 =
          case [i2 | i2 <- is2, Interval.member 1 (i1 * i2)] of
            [] -> error "AReal.recip: should not happen"
            [i2] -> i2
            is2'  -> go (Sturm.halve' c1 i1) [Sturm.halve' c2 i2 | i2 <- is2']

instance Real AReal where
  toRational x
    | isRational x =
        let p = minimalPolynomial x
            a = P.coeff (P.var X) p
            b = P.coeff P.mone p
        in - b / a
    | otherwise  = error "AReal.toRational: proper algebraic number"

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
    else Sturm.approx' (sturmChain a) (isolatingInterval a) epsilon

-- | Returns approximate interval such that @width (approxInterval a epsilon) <= epsilon@.
approxInterval
  :: AReal    -- ^ a
  -> Rational -- ^ epsilon
  -> Interval Rational
approxInterval a epsilon =
  if isRational a
    then Interval.singleton (toRational a)
    else Sturm.narrow' (sturmChain a) (isolatingInterval a) epsilon

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
    i2 = Sturm.narrow' chain (isolatingInterval a) (1/2)
    (Finite lb, inLB) = Interval.lowerBound' i2
    (Finite ub, inUB) = Interval.upperBound' i2
    ceiling_lb = ceiling lb
    ceiling_ub = ceiling ub
    i3 = NegInf <..<= fromInteger ceiling_lb

-- | Same as 'floor'.
floor' :: Integral b => AReal -> b
floor' a =
  if Sturm.numRoots' chain (Interval.intersection i2 i3) >= 1
    then fromInteger floor_ub
    else fromInteger floor_lb
  where
    chain = sturmChain a
    i2 = Sturm.narrow' chain (isolatingInterval a) (1/2)
    (Finite lb, inLB) = Interval.lowerBound' i2
    (Finite ub, inUB) = Interval.upperBound' i2
    floor_lb = floor lb
    floor_ub = floor ub
    i3 = fromInteger floor_ub <=..< PosInf

-- | The @n@th root of @a@
nthRoot :: Integer -> AReal -> AReal
nthRoot n a
  | n <= 0 = error "ToySolver.Data.AlgebraicNumver.Root.nthRoot"
  | even n =
      if a < 0
      then error "ToySolver.Data.AlgebraicNumver.Root.nthRoot: no real roots"
      else assert (length bs == 2) (maximum bs) -- select positive root
  | otherwise =
      assert (length bs == 1) (head bs) -- select unique root
  where
    bs = nthRoots n a

nthRoots :: Integer -> AReal -> [AReal]
nthRoots n _ | n <= 0 = []
nthRoots n a | even n && a < 0 = []
nthRoots n a = filter check (realRoots p2)
  where
    p1 = minimalPolynomial a
    p2 = rootNthRoot n p1
    c1 = sturmChain a
    ok0 = isolatingInterval a
    ng0 = map isolatingInterval $ delete a $ realRoots p1

    check :: AReal -> Bool
    check b = loop ok0 ng0 (isolatingInterval b)
      where
        c2 = sturmChain b
        loop ok ng i
          | Sturm.numRoots' c1 ok' == 0 = False
          | null ng'  = True
          | otherwise =
              loop (Sturm.halve' c1 ok')
                   (map (\i3 -> Sturm.halve' c1 i3) ng')
                   (Sturm.halve' c2 i)
          where
            i2  = i ^ n
            ok' = Interval.intersection i2 ok
            ng' = filter (\i3 -> Sturm.numRoots' c1 i3 /= 0) $
                    map (Interval.intersection i2) ng

-- | Same algebraic real, but represented using finer grained 'isolatingInterval'.
refineIsolatingInterval :: AReal -> AReal
refineIsolatingInterval a@(RealRoot p i) =
  if Interval.width i <= 0
    then a
    else RealRoot p (Sturm.halve p i)

{--------------------------------------------------------------------
  Properties
--------------------------------------------------------------------}

-- | The polynomial of which the algebraic number is root.
minimalPolynomial :: AReal -> UPolynomial Rational
minimalPolynomial (RealRoot p _) = p

sturmChain :: AReal -> Sturm.SturmChain
sturmChain a = Sturm.sturmChain (minimalPolynomial a)

-- | Isolating interval that separate the number from other roots of 'minimalPolynomial' of it.
isolatingInterval :: AReal -> Interval Rational
isolatingInterval (RealRoot _ i) = i

-- | Degree of the algebraic number.
--
-- If the algebraic number's 'minimalPolynomial' has degree @n@,
-- then the algebraic number is said to be degree @n@.
instance P.Degree AReal where
  deg a = P.deg $ minimalPolynomial a

-- | Whether the algebraic number is a rational.
isRational :: AReal -> Bool
isRational x = P.deg x == 1

-- | Whether the algebraic number is a root of a polynomial with integer
-- coefficients with leading coefficient @1@ (a monic polynomial).
isAlgebraicInteger :: AReal -> Bool
isAlgebraicInteger x = abs (P.lc P.nat (P.pp (minimalPolynomial x))) == 1

-- | Height of the algebraic number.
--
-- The height of an algebraic number is the greatest absolute value of the
-- coefficients of the irreducible and primitive polynomial with integral
-- rational coefficients.
height :: AReal -> Integer
height x = maximum [abs c | (c,_) <- P.terms $ P.pp $ minimalPolynomial x]

-- | root index, satisfying
--
-- @
-- 'realRoots' ('minimalPolynomial' a) !! rootIndex a == a
-- @
rootIndex :: AReal -> Int
rootIndex a = idx
  where
    as = realRoots' (minimalPolynomial a)
    Just idx = elemIndex a as

{--------------------------------------------------------------------
  Pretty printing
--------------------------------------------------------------------}

instance Pretty AReal where
  pPrintPrec lv prec r =
    maybeParens (prec > appPrec) $
      PP.hsep [PP.text "RealRoot", pPrintPrec lv (appPrec+1) p, PP.int (rootIndex r)]
    where
      p = minimalPolynomial r
      appPrec = 10

instance P.PrettyCoeff AReal where
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
    [_, root5] = sort $ realRoots' ((P.var X)^2 - 5)
