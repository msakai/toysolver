{-# LANGUAGE ScopedTypeVariables, TypeFamilies, BangPatterns, DeriveDataTypeable #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Polynomial
-- Copyright   :  (c) Masahiro Sakai 2012-2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (ScopedTypeVariables, TypeFamilies, BangPatterns, DeriveDataTypeable)
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
module Data.Polynomial
  (
  -- * Polynomial type
    Polynomial
  , UPolynomial
  , X (..)

  -- * Conversion
  , Variables (..)
  , constant
  , terms
  , fromTerms
  , coeffMap
  , fromCoeffMap
  , fromTerm

  -- * Query
  , Degree (..)
  , lt
  , lc
  , lm
  , coeff
  , lookupCoeff
  , isPrimitive
  , isRootOf

  -- * Operations
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

  -- * Operations for univariate polynomials
  , pdiv
  , pmod
  , pdivMod
  , pgcd
  , plcm
  , pgcd'

  -- * Term
  , Term
  , UTerm
  , tdeg
  , tmult
  , tdivides
  , tdiv
  , tderiv
  , tintegral

  -- * Monic monomial
  , Monomial
  , UMonomial
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

  -- * Monomial order
  , MonomialOrder
  , lex
  , revlex
  , grlex
  , grevlex

  -- * Pretty Printing
  , PrintOptions (..)
  , defaultPrintOptions
  , prettyPrint
  , PrettyCoeff (..)
  , PrettyVar (..)
  ) where

import Prelude hiding (lex)
import Control.DeepSeq
import Control.Exception (assert)
import Control.Monad
import Data.Data
import qualified Data.FiniteField as FF
import Data.Function
import Data.List
import Data.Monoid
import Data.Ratio
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.IntMap as IM
import Data.Typeable
import Data.VectorSpace
import qualified Text.PrettyPrint.HughesPJClass as PP
import Text.PrettyPrint.HughesPJClass (Doc, PrettyLevel, Pretty (..), prettyParen)

infixl 7  `pdiv`, `pmod`

{--------------------------------------------------------------------
  Classes
--------------------------------------------------------------------}

class Variables f where
  var       :: Ord v => v -> f v
  variables :: Ord v => f v -> Set.Set v

-- | total degree of a given polynomial
class Degree t where
  deg :: t -> Integer

{--------------------------------------------------------------------
  Polynomial type
--------------------------------------------------------------------}

-- | Polynomial over commutative ring r
newtype Polynomial k v = Polynomial{ coeffMap :: Map.Map (Monomial v) k }
  deriving (Eq, Ord, Typeable)

instance (Eq k, Num k, Ord v) => Num (Polynomial k v) where
  (+)      = plus
  (*)      = mult
  negate   = neg
  abs x    = x -- OK?
  signum _ = 1 -- OK?
  fromInteger x = constant (fromInteger x)

instance (Eq k, Num k, Ord v) => AdditiveGroup (Polynomial k v) where
  (^+^)   = plus
  zeroV   = zero
  negateV = neg

instance (Eq k, Num k, Ord v) => VectorSpace (Polynomial k v) where
  type Scalar (Polynomial k v) = k
  k *^ p = scale k p

instance (Show v, Ord v, Show k) => Show (Polynomial k v) where
  showsPrec d p  = showParen (d > 10) $
    showString "fromTerms " . shows (terms p)

instance (NFData k, NFData v) => NFData (Polynomial k v) where
  rnf (Polynomial m) = rnf m

instance (Eq k, Num k) => Variables (Polynomial k) where
  var x       = fromTerm (1, var x)
  variables p = Set.unions $ [variables mm | (_, mm) <- terms p]

instance Degree (Polynomial k v) where
  deg p
    | isZero p  = -1
    | otherwise = maximum [deg mm | (_,mm) <- terms p]

normalize :: (Eq k, Num k, Ord v) => Polynomial k v -> Polynomial k v
normalize (Polynomial m) = Polynomial (Map.filter (0/=) m)

asConstant :: Num k => Polynomial k v -> Maybe k
asConstant p =
  case terms p of
    [] -> Just 0
    [(c,xs)] | Map.null (mindicesMap xs) -> Just c
    _ -> Nothing

scale :: (Eq k, Num k, Ord v) => k -> Polynomial k v -> Polynomial k v
scale 0 _ = zero
scale 1 p = p
scale a (Polynomial m) = normalize $ Polynomial (Map.map (a*) m)

zero :: (Eq k, Num k, Ord v) => Polynomial k v
zero = Polynomial $ Map.empty

plus :: (Eq k, Num k, Ord v) => Polynomial k v -> Polynomial k v -> Polynomial k v
plus (Polynomial m1) (Polynomial m2) = normalize $ Polynomial $ Map.unionWith (+) m1 m2

neg :: (Eq k, Num k, Ord v) => Polynomial k v -> Polynomial k v
neg (Polynomial m) = Polynomial $ Map.map negate m

mult :: (Eq k, Num k, Ord v) => Polynomial k v -> Polynomial k v -> Polynomial k v
mult a b
  | Just c <- asConstant a = scale c b
  | Just c <- asConstant b = scale c a
mult (Polynomial m1) (Polynomial m2) = normalize $ Polynomial $ Map.fromListWith (+)
      [ (xs1 `mmult` xs2, c1*c2)
      | (xs1,c1) <- Map.toList m1, (xs2,c2) <- Map.toList m2
      ]

isZero :: Polynomial k v -> Bool
isZero (Polynomial m) = Map.null m

-- | construct a polynomial from a constant
constant :: (Eq k, Num k, Ord v) => k -> Polynomial k v
constant c = fromTerm (c, mone)

-- | construct a polynomial from a list of monomials
fromTerms :: (Eq k, Num k, Ord v) => [Term k v] -> Polynomial k v
fromTerms = normalize . Polynomial . Map.fromListWith (+) . map (\(c,xs) -> (xs,c))

fromCoeffMap :: (Eq k, Num k, Ord v) => Map.Map (Monomial v) k -> Polynomial k v
fromCoeffMap m = normalize $ Polynomial m

-- | construct a polynomial from a monomial
fromTerm :: (Eq k, Num k, Ord v) => Term k v -> Polynomial k v
fromTerm (c,xs) = normalize $ Polynomial $ Map.singleton xs c

-- | list of monomials
terms :: Polynomial k v -> [Term k v]
terms (Polynomial m) = [(c,xs) | (xs,c) <- Map.toList m]

-- | leading term with respect to a given monomial order
lt :: (Eq k, Num k, Ord v) => MonomialOrder v -> Polynomial k v -> Term k v
lt cmp p =
  case terms p of
    [] -> (0, mone) -- should be error?
    ms -> maximumBy (cmp `on` snd) ms

-- | leading coefficient with respect to a given monomial order
lc :: (Eq k, Num k, Ord v) => MonomialOrder v -> Polynomial k v -> k
lc cmp = fst . lt cmp

-- | leading monomial with respect to a given monomial order
lm :: (Eq k, Num k, Ord v) => MonomialOrder v -> Polynomial k v -> Monomial v
lm cmp = snd . lt cmp

coeff :: (Num k, Ord v) => Monomial v -> Polynomial k v -> k
coeff xs (Polynomial m) = Map.findWithDefault 0 xs m

lookupCoeff :: Ord v => Monomial v -> Polynomial k v -> Maybe k
lookupCoeff xs (Polynomial m) = Map.lookup xs m

contI :: (Integral r, Ord v) => Polynomial r v -> r
contI 0 = 1
contI p = foldl1' gcd [abs c | (c,_) <- terms p]

ppI :: (Integral r, Ord v) => Polynomial r v -> Polynomial r v
ppI p = mapCoeff f p
  where
    c = contI p
    f x = assert (x `mod` c == 0) $ x `div` c

class ContPP k where
  -- | Content of a polynomial  
  cont :: (Ord v) => Polynomial k v -> k
  -- constructive-algebra-0.3.0 では cont 0 は error になる

  -- | Primitive part of a polynomial
  pp :: (Ord v) => Polynomial k v -> Polynomial k v

instance ContPP Integer where
  cont = contI
  pp   = ppI

instance Integral r => ContPP (Ratio r) where
  {-# SPECIALIZE instance ContPP (Ratio Integer) #-}

  cont 0 = 1
  cont p = foldl1' gcd ns % foldl' lcm 1 ds
    where
      ns = [abs (numerator c) | (c,_) <- terms p]
      ds = [denominator c     | (c,_) <- terms p]  

  pp p = mapCoeff (/ c) p
    where
      c = cont p

isPrimitive :: (Eq k, Num k, ContPP k, Ord v) => Polynomial k v -> Bool
isPrimitive p = isZero p || cont p == 1

-- | Formal derivative of polynomials
deriv :: (Eq k, Num k, Ord v) => Polynomial k v -> v -> Polynomial k v
deriv p x = sumV [fromTerm (tderiv m x) | m <- terms p]

-- | Formal integral of polynomials
integral :: (Eq k, Fractional k, Ord v) => Polynomial k v -> v -> Polynomial k v
integral p x = sumV [fromTerm (tintegral m x) | m <- terms p]

-- | Evaluation
eval :: (Num k, Ord v) => (v -> k) -> Polynomial k v -> k
eval env p = sum [c * product [(env x) ^ e | (x,e) <- mindices xs] | (c,xs) <- terms p]

-- | Substitution or bind
subst
  :: (Eq k, Num k, Ord v1, Ord v2)
  => Polynomial k v1 -> (v1 -> Polynomial k v2) -> Polynomial k v2
subst p s =
  sumV [constant c * product [(s x)^e | (x,e) <- mindices xs] | (c, xs) <- terms p]

isRootOf :: (Eq k, Num k) => k -> UPolynomial k -> Bool
isRootOf x p = eval (\_ -> x) p == 0

mapCoeff :: (Eq k1, Num k1, Ord v) => (k -> k1) -> Polynomial k v -> Polynomial k1 v
mapCoeff f (Polynomial m) = Polynomial $ Map.mapMaybe g m
  where
    g x = if y == 0 then Nothing else Just y
      where
        y = f x

toMonic :: (Eq r, Fractional r, Ord v) => MonomialOrder v -> Polynomial r v -> Polynomial r v
toMonic cmp p
  | c == 0 || c == 1 = p
  | otherwise = mapCoeff (/c) p
  where
    c = lc cmp p

toUPolynomialOf :: (Ord k, Num k, Ord v) => Polynomial k v -> v -> UPolynomial (Polynomial k v)
toUPolynomialOf p v = fromTerms $ do
  (c,mm) <- terms p
  let m = mindicesMap mm
  return ( fromTerms [(c, mfromIndicesMap (Map.delete v m))]
         , var X `mpow` Map.findWithDefault 0 v m
         )

-- | Multivariate division algorithm
divModMP
  :: forall k v. (Eq k, Fractional k, Ord v)
  => MonomialOrder v -> Polynomial k v -> [Polynomial k v] -> ([Polynomial k v], Polynomial k v)
divModMP cmp p fs = go IM.empty p
  where
    ls = [(lt cmp f, f) | f <- fs]

    go :: IM.IntMap (Polynomial k v) -> Polynomial k v -> ([Polynomial k v], Polynomial k v)
    go qs g =
      case xs of
        [] -> ([IM.findWithDefault 0 i qs | i <- [0 .. length fs - 1]], g)
        (i, b, g') : _ -> go (IM.insertWith (+) i b qs) g'
      where
        ms = sortBy (flip cmp `on` snd) (terms g)
        xs = do
          (i,(a,f)) <- zip [0..] ls
          h <- ms
          guard $ a `tdivides` h
          let b = fromTerm $ tdiv h a
          return (i, b, g - b * f)

-- | Multivariate division algorithm
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

{--------------------------------------------------------------------
  Pretty printing
--------------------------------------------------------------------}

data PrintOptions k v
  = PrintOptions
  { pOptPrintVar        :: PrettyLevel -> Rational -> v -> Doc
  , pOptPrintCoeff      :: PrettyLevel -> Rational -> k -> Doc
  , pOptIsNegativeCoeff :: k -> Bool
  , pOptMonomialOrder   :: MonomialOrder v
  }

defaultPrintOptions :: (PrettyCoeff k, PrettyVar v, Ord v) => PrintOptions k v
defaultPrintOptions
  = PrintOptions
  { pOptPrintVar        = pPrintVar
  , pOptPrintCoeff      = pPrintCoeff
  , pOptIsNegativeCoeff = isNegativeCoeff
  , pOptMonomialOrder   = grlex
  }

instance (Ord k, Num k, Ord v, PrettyCoeff k, PrettyVar v) => Pretty (Polynomial k v) where
  pPrintPrec = prettyPrint defaultPrintOptions

prettyPrint
  :: (Ord k, Num k, Ord v)
  => PrintOptions k v
  -> PrettyLevel -> Rational -> Polynomial k v -> Doc
prettyPrint opt lv prec p =
    case sortBy (flip (pOptMonomialOrder opt) `on` snd) $ terms p of
      [] -> PP.int 0
      [t] -> pLeadingTerm prec t
      t:ts ->
        prettyParen (prec > addPrec) $
          PP.hcat (pLeadingTerm addPrec t : map pTrailingTerm ts)
    where
      pLeadingTerm prec (c,xs) =
        if pOptIsNegativeCoeff opt c
        then prettyParen (prec > addPrec) $
               PP.char '-' <> prettyPrintTerm opt lv (addPrec+1) (-c,xs)
        else prettyPrintTerm opt lv prec (c,xs)

      pTrailingTerm (c,xs) =
        if pOptIsNegativeCoeff opt c
        then PP.space <> PP.char '-' <> PP.space <> prettyPrintTerm opt lv (addPrec+1) (-c,xs)
        else PP.space <> PP.char '+' <> PP.space <> prettyPrintTerm opt lv (addPrec+1) (c,xs)

prettyPrintTerm
  :: (Ord k, Num k, Ord v)
  => PrintOptions k v
  -> PrettyLevel -> Rational -> Term k v -> Doc
prettyPrintTerm opt lv prec (c,xs)
  | len == 0  = pOptPrintCoeff opt lv (appPrec+1) c
    -- intentionally specify (appPrec+1) to parenthesize any composite expression
  | len == 1 && c == 1 = pPow prec $ head (mindices xs)
  | otherwise =
      prettyParen (prec > mulPrec) $
        PP.hcat $ intersperse (PP.char '*') fs
    where
      len = Map.size $ mindicesMap xs
      fs  = [pOptPrintCoeff opt lv (appPrec+1) c | c /= 1] ++ [pPow (mulPrec+1) p | p <- mindices xs]
      -- intentionally specify (appPrec+1) to parenthesize any composite expression

      pPow prec (x,1) = pOptPrintVar opt lv prec x
      pPow prec (x,n) =
        prettyParen (prec > expPrec) $
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
        prettyParen (p > ratPrec) $
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

data X = X
  deriving (Eq, Ord, Bounded, Enum, Show, Read, Typeable, Data)

instance NFData X

-- | division of univariate polynomials
pdiv :: (Eq k, Fractional k) => UPolynomial k -> UPolynomial k -> UPolynomial k
pdiv f1 f2 = fst (pdivMod f1 f2)

-- | division of univariate polynomials
pmod :: (Eq k, Fractional k) => UPolynomial k -> UPolynomial k -> UPolynomial k
pmod f1 f2 = snd (pdivMod f1 f2)

-- | division of univariate polynomials
pdivMod :: (Eq k, Fractional k) => UPolynomial k -> UPolynomial k -> (UPolynomial k, UPolynomial k)
pdivMod f g
  | isZero g  = error "pdivMod: division by zero"
  | otherwise = go 0 f
  where
    lt_g = lt lex g
    go !q !r
      | deg r < deg g = (q,r)
      | otherwise     = go (q + t) (r - t * g)
        where
          lt_r = lt lex r
          t    = fromTerm $ lt_r `tdiv` lt_g

-- | GCD of univariate polynomials
pgcd :: (Eq k, Fractional k) => UPolynomial k -> UPolynomial k -> UPolynomial k
pgcd f1 0  = toMonic grlex f1
pgcd f1 f2 = pgcd f2 (f1 `pmod` f2)

-- | LCM of univariate polynomials
plcm :: (Eq k, Fractional k) => UPolynomial k -> UPolynomial k -> UPolynomial k
plcm _ 0 = 0
plcm 0 _ = 0
plcm f1 f2 = toMonic grlex $ (f1 `pmod` (pgcd f1 f2)) * f2

-- | pseudo reminder
prem :: (Eq r, Integral r) => UPolynomial r -> UPolynomial r -> UPolynomial r
prem _ 0 = error "prem: division by 0"
prem f g
  | deg f < deg g = f
  | otherwise     = go (scale (lc_g ^ (deg f - deg g + 1)) f)
  where
    (lc_g, lm_g) = lt lex g
    deg_g    = deg g
    go !f1
      | deg_g > deg f1 = f1
      | otherwise =
          assert (lc_f1 `mod` lc_g == 0 && mdivides lm_g lm_f1) $
            go (f1 - fromTerm (lc_f1 `div` lc_g, lm_f1 `mdiv` lm_g) * g)
          where
            (lc_f1, lm_f1) = lt lex f1

-- | GCD of univariate polynomials
pgcd' :: (Eq r, Integral r) => UPolynomial r -> UPolynomial r -> UPolynomial r
pgcd' f1 0  = ppI f1
pgcd' f1 f2 = pgcd' f2 (f1 `prem` f2)

{--------------------------------------------------------------------
  Term
--------------------------------------------------------------------}

type Term k v = (k, Monomial v)
type UTerm k = Term k X

tdeg :: Term k v -> Integer
tdeg (_,xs) = deg xs

tmult :: (Num k, Ord v) => Term k v -> Term k v -> Term k v
tmult (c1,xs1) (c2,xs2) = (c1*c2, xs1 `mmult` xs2)

tdivides :: (Fractional k, Ord v) => Term k v -> Term k v -> Bool
tdivides (_,xs1) (_,xs2) = xs1 `mdivides` xs2

tdiv :: (Fractional k, Ord v) => Term k v -> Term k v -> Term k v
tdiv (c1,xs1) (c2,xs2) = (c1 / c2, xs1 `mdiv` xs2)

tderiv :: (Eq k, Num k, Ord v) => Term k v -> v -> Term k v
tderiv (c,xs) x =
  case mderiv xs x of
    (s,ys) -> (c * fromIntegral s, ys)

tintegral :: (Eq k, Fractional k, Ord v) => Term k v -> v -> Term k v
tintegral (c,xs) x =
  case mintegral xs x of
    (s,ys) -> (c * fromRational s, ys)

{--------------------------------------------------------------------
  Monic Monomial
--------------------------------------------------------------------}

-- 本当は変数の型に応じて type family で表現を変えたい

-- | Monic monomials
newtype Monomial v = Monomial{ mindicesMap :: Map.Map v Integer }
  deriving (Eq, Ord, Typeable)

type UMonomial = Monomial X

instance (Ord v, Show v) => Show (Monomial v) where
  showsPrec d m  = showParen (d > 10) $
    showString "mfromIndices " . shows (mindices m)

instance (NFData v) => NFData (Monomial v) where
  rnf (Monomial m) = rnf m

instance Degree (Monomial v) where
  deg (Monomial m) = sum $ Map.elems m

instance Variables Monomial where
  var x        = Monomial $ Map.singleton x 1
  variables mm = Map.keysSet (mindicesMap mm)

mnormalize :: Ord v => Monomial v -> Monomial v
mnormalize (Monomial m) = Monomial $ Map.filter (>0) m

mone :: Monomial v
mone = Monomial $ Map.empty

mfromIndices :: Ord v => [(v, Integer)] -> Monomial v
mfromIndices xs
  | any (\(_,e) -> 0>e) xs = error "mfromIndices: negative exponent"
  | otherwise = Monomial $ Map.fromListWith (+) [(x,e) | (x,e) <- xs, e > 0]

mfromIndicesMap :: Ord v => Map.Map v Integer -> Monomial v
mfromIndicesMap m
  | any (\(_,e) -> 0>e) (Map.toList m) = error "mfromIndicesMap: negative exponent"
  | otherwise = mnormalize $ Monomial m

mindices :: Ord v => Monomial v -> [(v, Integer)]
mindices = Map.toAscList . mindicesMap

mmult :: Ord v => Monomial v -> Monomial v -> Monomial v
mmult (Monomial xs1) (Monomial xs2) = mnormalize $ Monomial $ Map.unionWith (+) xs1 xs2

mpow :: Ord v => Monomial v -> Integer -> Monomial v
mpow _ 0 = mone
mpow m 1 = m
mpow (Monomial xs) e
  | 0 > e     = error "mpow: negative exponent"
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

{--------------------------------------------------------------------
  Monomial Order
--------------------------------------------------------------------}

type MonomialOrder v = Monomial v -> Monomial v -> Ordering

-- | Lexicographic order
lex :: Ord v => MonomialOrder v
lex xs1 xs2 = go (mindices xs1) (mindices xs2)
  where
    go [] [] = EQ
    go [] _  = LT -- = compare 0 n2
    go _ []  = GT -- = compare n1 0
    go ((x1,n1):xs1) ((x2,n2):xs2) =
      case compare x1 x2 of
        LT -> GT -- = compare n1 0
        GT -> LT -- = compare 0 n2
        EQ -> compare n1 n2 `mappend` go xs1 xs2

-- | Reverse lexicographic order
-- Note that revlex is NOT a monomial order.
revlex :: Ord v => Monomial v -> Monomial v -> Ordering
revlex xs1 xs2 = go (Map.toDescList (mindicesMap xs1)) (Map.toDescList (mindicesMap xs2))
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

-- | graded lexicographic order
grlex :: Ord v => MonomialOrder v
grlex = (compare `on` deg) `mappend` lex

-- | graded reverse lexicographic order
grevlex :: Ord v => MonomialOrder v
grevlex = (compare `on` deg) `mappend` revlex
