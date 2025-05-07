{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_HADDOCK show-extensions #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.Polynomial.Base
-- Copyright   :  (c) Masahiro Sakai 2012-2013
-- License     :  BSD-style
--
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable
--
-- Polynomials
--
-- References:
--
-- * Monomial order <http://en.wikipedia.org/wiki/Monomial_order>
--
-- * Polynomial class for Ruby <http://www.math.kobe-u.ac.jp/~kodama/tips-RubyPoly.html>
--
-- * constructive-algebra package <http://hackage.haskell.org/package/constructive-algebra>
--
-----------------------------------------------------------------------------
module ToySolver.Data.Polynomial.Base
  (
  -- * Polynomial type
    Polynomial

  -- * Conversion
  , Var (..)
  , constant
  , terms
  , fromTerms
  , coeffMap
  , fromCoeffMap
  , fromTerm

  -- * Query
  , Degree (..)
  , Vars (..)
  , lt
  , lc
  , lm
  , coeff
  , lookupCoeff
  , isPrimitive

  -- * Operations
  , Factor (..)
  , SQFree (..)
  , ContPP (..)
  , deriv
  , integral
  , eval
  , subst
  , mapCoeff
  , toMonic
  , toUPolynomialOf
  , divModMP
  , reduce

  -- * Univariate polynomials
  , UPolynomial
  , X (..)
  , UTerm
  , UMonomial
  , div
  , mod
  , divMod
  , divides
  , gcd
  , lcm
  , exgcd
  , pdivMod
  , pdiv
  , pmod
  , gcd'
  , isRootOf
  , isSquareFree
  , nat
  , eisensteinsCriterion

  -- * Term
  , Term
  , tdeg
  , tscale
  , tmult
  , tdivides
  , tdiv
  , tderiv
  , tintegral

  -- * Monic monomial
  , Monomial
  , mone
  , mfromIndices
  , mfromIndicesMap
  , mindices
  , mindicesMap
  , mmult
  , mpow
  , mdivides
  , mdiv
  , mderiv
  , mintegral
  , mlcm
  , mgcd
  , mcoprime

  -- * Monomial order
  , MonomialOrder
  , lex
  , revlex
  , grlex
  , grevlex

  -- * Pretty Printing
  , PrintOptions (..)
  , prettyPrint
  , PrettyCoeff (..)
  , PrettyVar (..)
  ) where

import Prelude hiding (lex, div, mod, divMod, gcd, lcm)
import qualified Prelude
import Control.DeepSeq
import Control.Exception (assert)
import Control.Monad
import Data.Default.Class
import Data.Data
import qualified Data.FiniteField as FF
import Data.Function
import Data.Hashable
import Data.List (foldl', foldl1', group, intersperse, maximumBy, sortBy)
import Data.Numbers.Primes (primeFactors)
import Data.Ratio
import Data.String (IsString (..))
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.VectorSpace
import qualified Text.PrettyPrint.HughesPJClass as PP
import Text.PrettyPrint.HughesPJClass (Doc, PrettyLevel, Pretty (..), maybeParens)

infixl 7  `div`, `mod`

{--------------------------------------------------------------------
  Classes
--------------------------------------------------------------------}

class Vars a v => Var a v | a -> v where
  var :: v -> a

class Ord v => Vars a v | a -> v where
  vars :: a -> Set v

-- | total degree of a given polynomial
class Degree t where
  deg :: t -> Integer

{--------------------------------------------------------------------
  Polynomial type
--------------------------------------------------------------------}

-- | Polynomial over commutative ring r
newtype Polynomial r v = Polynomial{ coeffMap :: Map (Monomial v) r }
  deriving (Eq, Ord, Typeable)

instance (Eq k, Num k, Ord v) => Num (Polynomial k v) where
  (+)      = plus
  (*)      = mult
  negate   = neg
  abs x    = x -- OK?
  signum _ = 1 -- OK?
  fromInteger x = constant (fromInteger x)

instance (Eq k, Num k, Ord v, IsString v) => IsString (Polynomial k v) where
  fromString s = var (fromString s)

instance (Eq k, Num k, Ord v) => AdditiveGroup (Polynomial k v) where
  (^+^)   = plus
  zeroV   = zero
  negateV = neg

instance (Eq k, Num k, Ord v) => VectorSpace (Polynomial k v) where
  type Scalar (Polynomial k v) = k
  k *^ p = scale k p

instance (Show v, Show k) => Show (Polynomial k v) where
  showsPrec d p  = showParen (d > 10) $
    showString "fromTerms " . shows (terms p)

instance (NFData k, NFData v) => NFData (Polynomial k v) where
  rnf (Polynomial m) = rnf m

instance (Hashable k, Hashable v) => Hashable (Polynomial k v) where
  hashWithSalt = hashUsing (Map.toList . coeffMap)

instance (Eq k, Num k, Ord v) => Var (Polynomial k v) v where
  var x = fromTerm (1, var x)

instance (Ord v) => Vars (Polynomial k v) v where
  vars p = Set.unions $ [vars mm | (_, mm) <- terms p]

instance Degree (Polynomial k v) where
  deg p
    | isZero p  = -1
    | otherwise = maximum [deg mm | (_,mm) <- terms p]

normalize :: (Eq k, Num k) => Polynomial k v -> Polynomial k v
normalize (Polynomial m) = Polynomial (Map.filter (0/=) m)

asConstant :: Num k => Polynomial k v -> Maybe k
asConstant p =
  case terms p of
    [] -> Just 0
    [(c,xs)] | Map.null (mindicesMap xs) -> Just c
    _ -> Nothing

scale :: (Eq k, Num k) => k -> Polynomial k v -> Polynomial k v
scale 0 _ = zero
scale 1 p = p
scale a (Polynomial m) = Polynomial (Map.mapMaybe f m)
  where
    f b = if c == 0 then Nothing else Just c
      where c = a * b

zero :: Polynomial k v
zero = Polynomial $ Map.empty

plus :: (Eq k, Num k, Ord v) => Polynomial k v -> Polynomial k v -> Polynomial k v
plus (Polynomial m1) (Polynomial m2) = Polynomial $ Map.mergeWithKey f id id m1 m2
  where
    f _ a b = if c == 0 then Nothing else Just c
      where
        c = a + b

neg :: (Num k) => Polynomial k v -> Polynomial k v
neg (Polynomial m) = Polynomial $ Map.map negate m

mult :: (Eq k, Num k, Ord v) => Polynomial k v -> Polynomial k v -> Polynomial k v
mult a b
  | Just c <- asConstant a = scale c b
  | Just c <- asConstant b = scale c a
mult (Polynomial m1) (Polynomial m2) = fromCoeffMap $ Map.fromListWith (+)
      [ (xs1 `mmult` xs2, c1*c2)
      | (xs1,c1) <- Map.toList m1, (xs2,c2) <- Map.toList m2
      ]

isZero :: Polynomial k v -> Bool
isZero (Polynomial m) = Map.null m

-- | construct a polynomial from a constant
constant :: (Eq k, Num k) => k -> Polynomial k v
constant c = fromTerm (c, mone)

-- | construct a polynomial from a list of terms
fromTerms :: (Eq k, Num k, Ord v) => [Term k v] -> Polynomial k v
fromTerms = fromCoeffMap . Map.fromListWith (+) . map (\(c,xs) -> (xs,c))

fromCoeffMap :: (Eq k, Num k) => Map (Monomial v) k -> Polynomial k v
fromCoeffMap m = normalize $ Polynomial m

-- | construct a polynomial from a singlet term
fromTerm :: (Eq k, Num k) => Term k v -> Polynomial k v
fromTerm (0,_) = zero
fromTerm (c,xs) = Polynomial $ Map.singleton xs c

-- | list of terms
terms :: Polynomial k v -> [Term k v]
terms (Polynomial m) = [(c,xs) | (xs,c) <- Map.toList m]

-- | leading term with respect to a given monomial order
lt :: (Num k) => MonomialOrder v -> Polynomial k v -> Term k v
lt cmp p =
  case terms p of
    [] -> (0, mone) -- should be error?
    ms -> maximumBy (cmp `on` snd) ms

-- | leading coefficient with respect to a given monomial order
lc :: (Num k) => MonomialOrder v -> Polynomial k v -> k
lc cmp = fst . lt cmp

-- | leading monomial with respect to a given monomial order
lm :: (Num k) => MonomialOrder v -> Polynomial k v -> Monomial v
lm cmp = snd . lt cmp

-- | Look up a coefficient for a given monomial.
-- If no such term exists, it returns @0@.
coeff :: (Num k, Ord v) => Monomial v -> Polynomial k v -> k
coeff xs (Polynomial m) = Map.findWithDefault 0 xs m

-- | Look up a coefficient for a given monomial.
-- If no such term exists, it returns @Nothing@.
lookupCoeff :: Ord v => Monomial v -> Polynomial k v -> Maybe k
lookupCoeff xs (Polynomial m) = Map.lookup xs m

contI :: (Integral r, Ord v) => Polynomial r v -> r
contI 0 = 1
contI p = foldl1' Prelude.gcd [abs c | (c,_) <- terms p]

ppI :: (Integral r, Ord v) => Polynomial r v -> Polynomial r v
ppI p = mapCoeff f p
  where
    c = contI p
    f x = assert (x `Prelude.mod` c == 0) $ x `Prelude.div` c

class ContPP k where
  type PPCoeff k

  -- | Content of a polynomial
  cont :: (Ord v) => Polynomial k v -> k
  -- constructive-algebra-0.3.0 では cont 0 は error になる

  -- | Primitive part of a polynomial
  pp :: (Ord v) => Polynomial k v -> Polynomial (PPCoeff k) v

instance ContPP Integer where
  type PPCoeff Integer = Integer
  cont = contI
  pp   = ppI

instance Integral r => ContPP (Ratio r) where
  {-# SPECIALIZE instance ContPP (Ratio Integer) #-}

  type PPCoeff (Ratio r) = r

  cont 0 = 1
  cont p = foldl1' Prelude.gcd ns % foldl' Prelude.lcm 1 ds
    where
      ns = [abs (numerator c) | (c,_) <- terms p]
      ds = [denominator c     | (c,_) <- terms p]

  pp p = mapCoeff (numerator . (/ c)) p
    where
      c = cont p

-- | a polynomial is called primitive if the greatest common divisor of its coefficients is 1.
isPrimitive :: (Eq k, Num k, ContPP k, Ord v) => Polynomial k v -> Bool
isPrimitive p = isZero p || cont p == 1

-- | Formal derivative of polynomials
deriv :: (Eq k, Num k, Ord v) => Polynomial k v -> v -> Polynomial k v
deriv p x = sumV [fromTerm (tderiv m x) | m <- terms p]

-- | Formal integral of polynomials
integral :: (Eq k, Fractional k, Ord v) => Polynomial k v -> v -> Polynomial k v
integral p x = sumV [fromTerm (tintegral m x) | m <- terms p]

-- | Evaluation
eval :: (Num k) => (v -> k) -> Polynomial k v -> k
eval env p = sum [c * product [(env x) ^ e | (x,e) <- mindices xs] | (c,xs) <- terms p]

-- | Substitution or bind
subst
  :: (Eq k, Num k, Ord v2)
  => Polynomial k v1 -> (v1 -> Polynomial k v2) -> Polynomial k v2
subst p s =
  sumV [constant c * product [(s x)^e | (x,e) <- mindices xs] | (c, xs) <- terms p]

-- | Transform polynomial coefficients.
mapCoeff :: (Eq k1, Num k1) => (k -> k1) -> Polynomial k v -> Polynomial k1 v
mapCoeff f (Polynomial m) = Polynomial $ Map.mapMaybe g m
  where
    g x = if y == 0 then Nothing else Just y
      where
        y = f x

-- | Transform a polynomial into a monic polynomial with respect to the given monomial order.
toMonic :: (Eq r, Fractional r) => MonomialOrder v -> Polynomial r v -> Polynomial r v
toMonic cmp p
  | c == 0 || c == 1 = p
  | otherwise = mapCoeff (/c) p
  where
    c = lc cmp p

-- | Convert /K[x,x1,x2,…]/ into /K[x1,x2,…][x]/.
toUPolynomialOf :: (Ord k, Num k, Ord v) => Polynomial k v -> v -> UPolynomial (Polynomial k v)
toUPolynomialOf p v = fromTerms $ do
  (c,mm) <- terms p
  let m = mindicesMap mm
  return ( fromTerms [(c, mfromIndicesMap (Map.delete v m))]
         , var X `mpow` Map.findWithDefault 0 v m
         )

-- | Multivariate division algorithm
--
-- @divModMP cmp f [g1,g2,..]@ returns a pair @([q1,q2,…],r)@ such that
--
--   * @f = g1*q1 + g2*q2 + .. + r@ and
--
--   * @g1, g2, ..@ do not divide @r@.
divModMP
  :: forall k v. (Eq k, Fractional k, Ord v)
  => MonomialOrder v -> Polynomial k v -> [Polynomial k v] -> ([Polynomial k v], Polynomial k v)
divModMP cmp p fs = go IntMap.empty (terms' p)
  where
    terms' :: Polynomial k v -> [Term k v]
    terms' g = sortBy (flip cmp `on` snd) (terms g)

    merge :: [Term k v] -> [Term k v] -> [Term k v]
    merge [] ys = ys
    merge xs [] = xs
    merge xxs@(x:xs) yys@(y:ys) =
      case cmp (snd x) (snd y) of
        GT -> x : merge xs yys
        LT -> y : merge xxs ys
        EQ ->
          case fst x + fst y of
            0 -> merge xs ys
            c -> (c, snd x) : merge xs ys

    ls = zip [0..] [(lt cmp f, terms' f) | f <- fs]

    go :: IntMap (Polynomial k v) -> [Term k v] -> ([Polynomial k v], Polynomial k v)
    go qs g =
      case xs of
        [] -> ([IntMap.findWithDefault 0 i qs | i <- [0 .. length fs - 1]], fromTerms g)
        (i, b, g') : _ -> go (IntMap.insertWith (+) i b qs) g'
      where
        xs = do
          (i,(a,f)) <- ls
          h <- g
          guard $ a `tdivides` h
          let b = tdiv h a
          return (i, fromTerm b, merge g [(tscale (-1) b `tmult` m) | m <- f])

-- | Multivariate division algorithm
--
-- @reduce cmp f gs = snd (divModMP cmp f gs)@
reduce
  :: (Eq k, Fractional k, Ord v)
  => MonomialOrder v -> Polynomial k v -> [Polynomial k v] -> Polynomial k v
reduce cmp p fs = go p
  where
    ls = [(lt cmp f, f) | f <- fs]
    go g = if null xs then g else go (head xs)
      where
        ms = sortBy (flip cmp `on` snd) (terms g)
        xs = do
          (a,f) <- ls
          h <- ms
          guard $ a `tdivides` h
          return (g - fromTerm (tdiv h a) * f)

-- | Prime factorization of polynomials
class Factor a where
  -- | factor a polynomial @p@ into @p1 ^ n1 * p2 ^ n2 * ..@ and
  -- return a list @[(p1,n1), (p2,n2), ..]@.
  factor :: a -> [(a, Integer)]

-- | Square-free factorization of polynomials
class SQFree a where
  -- | factor a polynomial @p@ into @p1 ^ n1 * p2 ^ n2 * ..@ and
  -- return a list @[(p1,n1), (p2,n2), ..]@.
  sqfree :: a -> [(a, Integer)]

-- | Eisenstein's irreducibility criterion.
--
-- Given a polynomial with integer coefficients @P[x] = an x^n + .. + a1*x + a0@,
-- it is irreducible over rational numbers if there exists a prime number @p@
-- satisfying the following conditions:
--
-- * @p@ divides ai for @i /= n@,
--
-- * @p@ does not divides @an@, and
--
-- * @p^2@ does not divides @a0@.
--
eisensteinsCriterion
  :: (ContPP k, PPCoeff k ~ Integer)
  => UPolynomial k -> Bool
eisensteinsCriterion p
  | deg p <= 1 = True
  | otherwise  = eisensteinsCriterion' (pp p)

eisensteinsCriterion' :: UPolynomial Integer -> Bool
eisensteinsCriterion' p = or [criterion prime | prime <- map head $ group $ primeFactors c]
  where
    Just ((_,an), ts) = Map.maxViewWithKey (coeffMap p)
    a0 = coeff mone p
    c = foldl' Prelude.gcd 0 [ai | (_,ai) <- Map.toList ts]
    criterion prime = an `Prelude.mod` prime /= 0 && a0 `Prelude.mod` (prime*prime) /= 0

{--------------------------------------------------------------------
  Pretty printing
--------------------------------------------------------------------}

-- | Options for pretty printing polynomials
--
-- The default value can be obtained by 'def'.
data PrintOptions k v
  = PrintOptions
  { pOptPrintVar        :: PrettyLevel -> Rational -> v -> Doc
  , pOptPrintCoeff      :: PrettyLevel -> Rational -> k -> Doc
  , pOptIsNegativeCoeff :: k -> Bool
  , pOptMonomialOrder   :: MonomialOrder v
  }

instance (PrettyCoeff k, PrettyVar v, Ord v) => Default (PrintOptions k v) where
  def =
    PrintOptions
    { pOptPrintVar        = pPrintVar
    , pOptPrintCoeff      = pPrintCoeff
    , pOptIsNegativeCoeff = isNegativeCoeff
    , pOptMonomialOrder   = grlex
    }

instance (Ord k, Num k, Ord v, PrettyCoeff k, PrettyVar v) => Pretty (Polynomial k v) where
  pPrintPrec = prettyPrint def

prettyPrint
  :: (Ord k, Num k)
  => PrintOptions k v
  -> PrettyLevel -> Rational -> Polynomial k v -> Doc
prettyPrint opt lv prec p =
    case sortBy (flip (pOptMonomialOrder opt) `on` snd) $ terms p of
      [] -> PP.int 0
      [t] -> pLeadingTerm prec t
      t:ts ->
        maybeParens (prec > addPrec) $
          PP.hcat (pLeadingTerm addPrec t : map pTrailingTerm ts)
    where
      pLeadingTerm prec' (c,xs) =
        if pOptIsNegativeCoeff opt c
        then maybeParens (prec' > addPrec) $
               PP.char '-' <> prettyPrintTerm opt lv (addPrec+1) (-c,xs)
        else prettyPrintTerm opt lv prec' (c,xs)

      pTrailingTerm (c,xs) =
        if pOptIsNegativeCoeff opt c
        then PP.space <> PP.char '-' <> PP.space <> prettyPrintTerm opt lv (addPrec+1) (-c,xs)
        else PP.space <> PP.char '+' <> PP.space <> prettyPrintTerm opt lv (addPrec+1) (c,xs)

prettyPrintTerm
  :: (Ord k, Num k)
  => PrintOptions k v
  -> PrettyLevel -> Rational -> Term k v -> Doc
prettyPrintTerm opt lv prec (c,xs)
  | len == 0  = pOptPrintCoeff opt lv (appPrec+1) c
    -- intentionally specify (appPrec+1) to parenthesize any composite expression
  | len == 1 && c == 1 = pPow prec $ head (mindices xs)
  | otherwise =
      maybeParens (prec > mulPrec) $
        PP.hcat $ intersperse (PP.char '*') fs
    where
      len = Map.size $ mindicesMap xs
      fs  = [pOptPrintCoeff opt lv (appPrec+1) c | c /= 1] ++ [pPow (mulPrec+1) p | p <- mindices xs]
      -- intentionally specify (appPrec+1) to parenthesize any composite expression

      pPow prec' (x,1) = pOptPrintVar opt lv prec' x
      pPow prec' (x,n) =
        maybeParens (prec' > expPrec) $
          pOptPrintVar opt lv (expPrec+1) x <> PP.char '^' <> PP.integer n

class PrettyCoeff a where
  pPrintCoeff :: PrettyLevel -> Rational -> a -> Doc
  isNegativeCoeff :: a -> Bool
  isNegativeCoeff _ = False

instance PrettyCoeff Integer where
  pPrintCoeff = pPrintPrec
  isNegativeCoeff = (0>)

instance (PrettyCoeff a, Integral a) => PrettyCoeff (Ratio a) where
  pPrintCoeff lv p r
    | denominator r == 1 = pPrintCoeff lv p (numerator r)
    | otherwise =
        maybeParens (p > ratPrec) $
          pPrintCoeff lv (ratPrec+1) (numerator r) <>
          PP.char '/' <>
          pPrintCoeff lv (ratPrec+1) (denominator r)
  isNegativeCoeff x = isNegativeCoeff (numerator x)

instance PrettyCoeff (FF.PrimeField a) where
  pPrintCoeff lv p a = pPrintCoeff lv p (FF.toInteger a)
  isNegativeCoeff _  = False

instance (Num c, Ord c, PrettyCoeff c, Ord v, PrettyVar v) => PrettyCoeff (Polynomial c v) where
  pPrintCoeff = pPrintPrec

class PrettyVar a where
  pPrintVar :: PrettyLevel -> Rational -> a -> Doc

instance PrettyVar Int where
  pPrintVar _ _ n = PP.char 'x' <> PP.int n

instance PrettyVar X where
  pPrintVar _ _ X = PP.char 'x'

addPrec, mulPrec, ratPrec, expPrec, appPrec :: Rational
addPrec = 6 -- Precedence of '+'
mulPrec = 7 -- Precedence of '*'
ratPrec = 7 -- Precedence of '/'
expPrec = 8 -- Precedence of '^'
appPrec = 10 -- Precedence of function application

{--------------------------------------------------------------------
  Univariate polynomials
--------------------------------------------------------------------}

-- | Univariate polynomials over commutative ring r
type UPolynomial r = Polynomial r X

-- | Variable "x"
data X = X
  deriving (Eq, Ord, Bounded, Enum, Show, Read, Typeable, Data)

instance NFData X where
   rnf a = a `seq` ()

instance Hashable X where
  hashWithSalt = hashUsing fromEnum

-- | Natural ordering /x^0 < x^1 < x^2 ../ is the unique monomial order for
-- univariate polynomials.
nat :: MonomialOrder X
nat = compare `on` deg

-- | division of univariate polynomials
div :: (Eq k, Fractional k) => UPolynomial k -> UPolynomial k -> UPolynomial k
div f1 f2 = fst (divMod f1 f2)

-- | division of univariate polynomials
mod :: (Eq k, Fractional k) => UPolynomial k -> UPolynomial k -> UPolynomial k
mod f1 f2 = snd (divMod f1 f2)

-- | division of univariate polynomials
divMod :: (Eq k, Fractional k) => UPolynomial k -> UPolynomial k -> (UPolynomial k, UPolynomial k)
divMod f g
  | isZero g  = error "ToySolver.Data.Polynomial.divMod: division by zero"
  | otherwise = go 0 f
  where
    lt_g = lt nat g
    go !q !r
      | deg r < deg g = (q,r)
      | otherwise     = go (q + t) (r - t * g)
        where
          lt_r = lt nat r
          t    = fromTerm $ lt_r `tdiv` lt_g

divides :: (Eq k, Fractional k) => UPolynomial k -> UPolynomial k -> Bool
divides f1 f2 = f2 `mod` f1 == 0

-- | GCD of univariate polynomials
gcd :: (Eq k, Fractional k) => UPolynomial k -> UPolynomial k -> UPolynomial k
gcd f1 0  = toMonic nat f1
gcd f1 f2 = gcd f2 (f1 `mod` f2)

-- | LCM of univariate polynomials
lcm :: (Eq k, Fractional k) => UPolynomial k -> UPolynomial k -> UPolynomial k
lcm _ 0 = 0
lcm 0 _ = 0
lcm f1 f2 = toMonic nat $ (f1 `mod` (gcd f1 f2)) * f2

-- | Extended GCD algorithm
exgcd
  :: (Eq k, Fractional k)
  => UPolynomial k
  -> UPolynomial k
  -> (UPolynomial k, UPolynomial k, UPolynomial k)
exgcd f1 f2 = f $ go f1 f2 1 0 0 1
  where
    go !r0 !r1 !s0 !s1 !t0 !t1
      | r1 == 0   = (r0, s0, t0)
      | otherwise = go r1 r2 s1 s2 t1 t2
      where
        (q, r2) = r0 `divMod` r1
        s2 = s0 - q*s1
        t2 = t0 - q*t1
    f (g,u,v)
      | lc_g == 0 = (g, u, v)
      | otherwise = (mapCoeff (/lc_g) g, mapCoeff (/lc_g) u, mapCoeff (/lc_g) v)
      where
        lc_g = lc nat g

-- | pseudo division
pdivMod :: (Eq r, Num r) => UPolynomial r -> UPolynomial r -> (r, UPolynomial r, UPolynomial r)
pdivMod _ 0 = error "ToySolver.Data.Polynomial.pdivMod: division by 0"
pdivMod f g
  | deg f < deg g = (1, 0, f)
  | otherwise     = go (deg f - deg g + 1) f 0
  where
    (lc_g, lm_g) = lt nat g
    b = lc_g ^ (deg f - deg_g + 1)
    deg_g = deg g
    go !n !f1 !q
      | deg_g > deg f1 = (b, q, scale (lc_g ^ n) f1)
      | otherwise      = go (n - 1) (scale lc_g f1 - s * g) (q + scale (lc_g ^ (n-1)) s)
          where
            (lc_f1, lm_f1) = lt nat f1
            s = fromTerm (lc_f1, lm_f1 `mdiv` lm_g)

-- | pseudo quotient
pdiv :: (Eq r, Num r) => UPolynomial r -> UPolynomial r -> UPolynomial r
pdiv f g =
  case f `pdivMod` g of
    (_, q, _) -> q

-- | pseudo reminder
pmod :: (Eq r, Num r) => UPolynomial r -> UPolynomial r -> UPolynomial r
pmod _ 0 = error "ToySolver.Data.Polynomial.pmod: division by 0"
pmod f g
  | deg f < deg g = f
  | otherwise     = go (deg f - deg g + 1) f
  where
    (lc_g, lm_g) = lt nat g
    deg_g = deg g
    go !n !f1
      | deg_g > deg f1 = scale (lc_g ^ n) f1
      | otherwise      = go (n - 1) (scale lc_g f1 - s * g)
          where
            (lc_f1, lm_f1) = lt nat f1
            s = fromTerm (lc_f1, lm_f1 `mdiv` lm_g)

-- | GCD of univariate polynomials
gcd' :: (Integral r) => UPolynomial r -> UPolynomial r -> UPolynomial r
gcd' f1 0  = ppI f1
gcd' f1 f2 = gcd' f2 (f1 `pmod` f2)

-- | Is the number a root of the polynomial?
isRootOf :: (Eq k, Num k) => k -> UPolynomial k -> Bool
isRootOf x p = eval (\_ -> x) p == 0

-- | Is the polynomial square free?
isSquareFree :: (Eq k, Fractional k) => UPolynomial k -> Bool
isSquareFree p = gcd p (deriv p X) == 1

{--------------------------------------------------------------------
  Term
--------------------------------------------------------------------}

type Term k v = (k, Monomial v)

type UTerm k = Term k X

tdeg :: Term k v -> Integer
tdeg (_,xs) = deg xs

tscale :: (Num k) => k -> Term k v -> Term k v
tscale a (c, xs) = (a*c, xs)

tmult :: (Num k, Ord v) => Term k v -> Term k v -> Term k v
tmult (c1,xs1) (c2,xs2) = (c1*c2, xs1 `mmult` xs2)

tdivides :: (Ord v) => Term k v -> Term k v -> Bool
tdivides (_,xs1) (_,xs2) = xs1 `mdivides` xs2

tdiv :: (Fractional k, Ord v) => Term k v -> Term k v -> Term k v
tdiv (c1,xs1) (c2,xs2) = (c1 / c2, xs1 `mdiv` xs2)

tderiv :: (Num k, Ord v) => Term k v -> v -> Term k v
tderiv (c,xs) x =
  case mderiv xs x of
    (s,ys) -> (c * fromIntegral s, ys)

tintegral :: (Fractional k, Ord v) => Term k v -> v -> Term k v
tintegral (c,xs) x =
  case mintegral xs x of
    (s,ys) -> (c * fromRational s, ys)

{--------------------------------------------------------------------
  Monic Monomial
--------------------------------------------------------------------}

-- 本当は変数の型に応じて type family で表現を変えたい

-- | Monic monomials
newtype Monomial v = Monomial{ mindicesMap :: Map v Integer }
  deriving (Eq, Ord, Typeable)

type UMonomial = Monomial X

instance (Show v) => Show (Monomial v) where
  showsPrec d m  = showParen (d > 10) $
    showString "mfromIndices " . shows (mindices m)

instance (Ord v, IsString v) => IsString (Monomial v) where
  fromString s = var (fromString s)

instance (NFData v) => NFData (Monomial v) where
  rnf (Monomial m) = rnf m

instance Degree (Monomial v) where
  deg (Monomial m) = sum $ Map.elems m

instance Ord v => Var (Monomial v) v where
  var x = Monomial $ Map.singleton x 1

instance Ord v => Vars (Monomial v) v where
  vars mm = Map.keysSet (mindicesMap mm)

instance Hashable v => Hashable (Monomial v) where
  hashWithSalt = hashUsing (Map.toList . mindicesMap)

mone :: Monomial v
mone = Monomial $ Map.empty

mfromIndices :: Ord v => [(v, Integer)] -> Monomial v
mfromIndices xs
  | any (\(_,e) -> 0>e) xs = error "ToySolver.Data.Polynomial.mfromIndices: negative exponent"
  | otherwise = Monomial $ Map.fromListWith (+) [(x,e) | (x,e) <- xs, e > 0]

mfromIndicesMap :: Ord v => Map v Integer -> Monomial v
mfromIndicesMap m
  | any (\(_,e) -> 0>e) (Map.toList m) = error "ToySolver.Data.Polynomial.mfromIndicesMap: negative exponent"
  | otherwise = mfromIndicesMap' m

mfromIndicesMap' :: Map v Integer -> Monomial v
mfromIndicesMap' m = Monomial $ Map.filter (>0) m

mindices :: Monomial v -> [(v, Integer)]
mindices = Map.toAscList . mindicesMap

mmult :: Ord v => Monomial v -> Monomial v -> Monomial v
mmult (Monomial xs1) (Monomial xs2) = mfromIndicesMap' $ Map.unionWith (+) xs1 xs2

mpow :: Ord v => Monomial v -> Integer -> Monomial v
mpow _ 0 = mone
mpow m 1 = m
mpow (Monomial xs) e
  | 0 > e     = error "ToySolver.Data.Polynomial.mpow: negative exponent"
  | otherwise = Monomial $ Map.map (e*) xs

mdivides :: Ord v => Monomial v -> Monomial v -> Bool
mdivides (Monomial xs1) (Monomial xs2) = Map.isSubmapOfBy (<=) xs1 xs2

mdiv :: Ord v => Monomial v -> Monomial v -> Monomial v
mdiv (Monomial xs1) (Monomial xs2) = Monomial $ Map.differenceWith f xs1 xs2
  where
    f m n
      | m <= n    = Nothing
      | otherwise = Just (m - n)

mderiv :: Ord v => Monomial v -> v -> (Integer, Monomial v)
mderiv (Monomial xs) x
  | n==0      = (0, mone)
  | otherwise = (n, Monomial $ Map.update f x xs)
  where
    n = Map.findWithDefault 0 x xs
    f m
      | m <= 1    = Nothing
      | otherwise = Just $! m - 1

mintegral :: Ord v => Monomial v -> v -> (Rational, Monomial v)
mintegral (Monomial xs) x =
  (1 % fromIntegral (n + 1), Monomial $ Map.insert x (n+1) xs)
  where
    n = Map.findWithDefault 0 x xs

mlcm :: Ord v => Monomial v -> Monomial v -> Monomial v
mlcm (Monomial m1) (Monomial m2) = Monomial $ Map.unionWith max m1 m2

mgcd :: Ord v => Monomial v -> Monomial v -> Monomial v
mgcd (Monomial m1) (Monomial m2) = Monomial $ Map.intersectionWith min m1 m2

mcoprime :: Ord v => Monomial v -> Monomial v -> Bool
mcoprime m1 m2 = mgcd m1 m2 == mone

{--------------------------------------------------------------------
  Monomial Order
--------------------------------------------------------------------}

type MonomialOrder v = Monomial v -> Monomial v -> Ordering

-- | Lexicographic order
lex :: Ord v => MonomialOrder v
lex = go `on` mindices
  where
    go [] [] = EQ
    go [] _  = LT -- = compare 0 n2
    go _ []  = GT -- = compare n1 0
    go ((x1,n1):xs1) ((x2,n2):xs2) =
      case compare x1 x2 of
        LT -> GT -- = compare n1 0
        GT -> LT -- = compare 0 n2
        EQ -> compare n1 n2 `mappend` go xs1 xs2

-- | Reverse lexicographic order.
--
-- Note that revlex is /NOT/ a monomial order.
revlex :: Ord v => Monomial v -> Monomial v -> Ordering
revlex = go `on` (Map.toDescList . mindicesMap)
  where
    go [] [] = EQ
    go [] _  = GT -- = cmp 0 n2
    go _ []  = LT -- = cmp n1 0
    go ((x1,n1):xs1) ((x2,n2):xs2) =
      case compare x1 x2 of
        LT -> GT -- = cmp 0 n2
        GT -> LT -- = cmp n1 0
        EQ -> cmp n1 n2 `mappend` go xs1 xs2
    cmp n1 n2 = compare n2 n1

-- | Graded lexicographic order
grlex :: Ord v => MonomialOrder v
grlex = (compare `on` deg) `mappend` lex

-- | Graded reverse lexicographic order
grevlex :: Ord v => MonomialOrder v
grevlex = (compare `on` deg) `mappend` revlex
