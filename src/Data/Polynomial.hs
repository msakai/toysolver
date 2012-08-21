{-# LANGUAGE ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, TypeSynonymInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Polynomial
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, TypeSynonymInstances)
--
-- Polynomials
--
-- References:
--
-- * Monomial order <http://en.wikipedia.org/wiki/Monomial_order>
-- 
-- * Gröbner basis <http://en.wikipedia.org/wiki/Gr%C3%B6bner_basis>
--
-- * グレブナー基底 <http://d.hatena.ne.jp/keyword/%A5%B0%A5%EC%A5%D6%A5%CA%A1%BC%B4%F0%C4%EC>
--
-- * Gröbner Bases and Buchberger’s Algorithm <http://math.rice.edu/~cbruun/vigre/vigreHW6.pdf>
--
-- * Polynomial class for Ruby <http://www.math.kobe-u.ac.jp/~kodama/tips-RubyPoly.html>
--
-- * Docon <http://www.haskell.org/docon/>
--
-- * constructive-algebra package <http://hackage.haskell.org/package/constructive-algebra>
-- 
-----------------------------------------------------------------------------
module Data.Polynomial
  (
  -- * Polynomial type
    Polynomial
  , UPolynomial

  -- * Conversion
  , var
  , constant
  , terms
  , fromTerms
  , coeffMap
  , fromCoeffMap
  , fromMonomial

  -- * Query
  , leadingTerm
  , deg
  , coeff
  , lookupCoeff

  -- * Operations
  , deriv
  , integral
  , eval
  , evalM
  , subst
  , isRootOf
  , mapVar
  , mapCoeff
  , toMonic
  , toZ
  , polyDiv
  , polyMod
  , polyDivMod
  , polyGCD
  , polyLCM
  , polyMDivMod
  , reduce

  -- * Monomial
  , Monomial
  , monomialDegree
  , monomialProd
  , monomialDivisible
  , monomialDiv
  , monomialDeriv
  , monomialIntegral

  -- * Monic monomial
  , MonicMonomial
  , mmVar
  , mmOne
  , mmFromList
  , mmToList
  , mmToIntMap
  , mmDegree
  , mmProd
  , mmDivisible
  , mmDiv
  , mmDeriv
  , mmIntegral
  , mmLCM
  , mmGCD
  , mmMapVar

  -- * Monomial order
  , MonomialOrder
  , lex
  , revlex
  , grlex
  , grevlex

  -- * Utility functions
  , render
  , renderWith
  , RenderCoeff (..)
  , RenderVar (..)
  ) where

import Prelude hiding (lex)
import Control.Monad
import Data.Function
import Data.List
import Data.Monoid
import Data.Ratio
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.IntMap as IM

import Data.Linear

{--------------------------------------------------------------------
  Polynomial type
--------------------------------------------------------------------}

-- | Polynomial over commutative ring r
newtype Polynomial k v = Polynomial{ coeffMap :: Map.Map (MonicMonomial v) k }
  deriving (Eq, Ord)

-- | Univalent polynomials over commutative ring r
type UPolynomial r = Polynomial r ()

instance (Eq k, Num k, Ord v, Show v) => Num (Polynomial k v) where
  Polynomial m1 + Polynomial m2 = normalize $ Polynomial $ Map.unionWith (+) m1 m2
  Polynomial m1 * Polynomial m2 = normalize $ Polynomial $ Map.fromListWith (+)
      [ (xs1 `mmProd` xs2, c1*c2)
      | (xs1,c1) <- Map.toList m1, (xs2,c2) <- Map.toList m2
      ]
  negate (Polynomial m) = Polynomial $ Map.map negate m
  abs x = x    -- OK?
  signum x = 1 -- OK?
  fromInteger x = constant (fromInteger x)

instance (Eq k, Num k, Ord v, Show v) => Module k (Polynomial k v) where
  k .*. p = constant k * p
  p .+. q = p + q
  lzero = 0

instance (Eq k, Fractional k, Ord v, Show v) => Linear k (Polynomial k v)

instance (Show v, Ord v, Show k) => Show (Polynomial k v) where
  showsPrec d p  = showParen (d > 10) $
    showString "fromTerms " . shows (terms p)

normalize :: (Eq k, Num k, Ord v) => Polynomial k v -> Polynomial k v
normalize (Polynomial m) = Polynomial (Map.filter (0/=) m)

-- | construct a polynomial from a variable
var :: (Eq k, Num k, Ord v) => v -> Polynomial k v
var x = fromMonomial (1, mmVar x)

-- | construct a polynomial from a constant
constant :: (Eq k, Num k, Ord v) => k -> Polynomial k v
constant c = fromMonomial (c, mmOne)

-- | construct a polynomial from a list of monomials
fromTerms :: (Eq k, Num k, Ord v) => [Monomial k v] -> Polynomial k v
fromTerms = normalize . Polynomial . Map.fromListWith (+) . map (\(c,xs) -> (xs,c))

fromCoeffMap :: (Eq k, Num k, Ord v) => Map.Map (MonicMonomial v) k -> Polynomial k v
fromCoeffMap m = normalize $ Polynomial m

-- | construct a polynomial from a monomial
fromMonomial :: (Eq k, Num k, Ord v) => Monomial k v -> Polynomial k v
fromMonomial (c,xs) = normalize $ Polynomial $ Map.singleton xs c

-- | list of monomials
terms :: Polynomial k v -> [Monomial k v]
terms (Polynomial m) = [(c,xs) | (xs,c) <- Map.toList m]

-- | leading term with respect to a given monomial order
leadingTerm :: (Eq k, Num k, Ord v) => MonomialOrder v -> Polynomial k v -> Monomial k v
leadingTerm cmp p =
  case terms p of
    [] -> (0, mmOne) -- should be error?
    ms -> maximumBy (cmp `on` snd) ms

-- | total degree of a given polynomial
deg :: Polynomial k v -> Integer
deg = maximum . (0:) . map monomialDegree . terms

coeff :: (Num k, Ord v) => MonicMonomial v -> Polynomial k v -> k
coeff xs (Polynomial m) = Map.findWithDefault 0 xs m

lookupCoeff :: Ord v => MonicMonomial v -> Polynomial k v -> Maybe k
lookupCoeff xs (Polynomial m) = Map.lookup xs m

-- | Formal derivative of polynomials
deriv :: (Eq k, Num k, Ord v, Show v) => Polynomial k v -> v -> Polynomial k v
deriv p x = sum [fromMonomial (monomialDeriv m x) | m <- terms p]

-- | Formal integral of polynomials
integral :: (Eq k, Fractional k, Ord v, Show v) => Polynomial k v -> v -> Polynomial k v
integral p x = sum [fromMonomial (monomialIntegral m x) | m <- terms p]

-- | Evaluation
eval :: (Num k, Ord v) => (v -> k) -> Polynomial k v -> k
eval env p = sum [c * product [(env x) ^ e | (x,e) <- mmToList xs] | (c,xs) <- terms p]

-- | Monadic evaluation
evalM :: (Num k, Ord v, Monad m) => (v -> m k) -> Polynomial k v -> m k
evalM env p = do
  liftM sum $ forM (terms p) $ \(c,xs) -> do
    rs <- mapM (\(x,e) -> liftM (^ e) (env x)) (mmToList xs)
    return (c * product rs)

-- | Substitution or bind
subst :: (Num k, Eq k, Ord v1, Ord v2, Show v2) => Polynomial k v1 -> (v1 -> Polynomial k v2) -> Polynomial k v2
subst p s =
  sum [constant c * product [(s x)^e | (x,e) <- mmToList xs] | (c, xs) <- terms p]

isRootOf :: (Num k, Eq k) => k -> UPolynomial k -> Bool
isRootOf x p = eval (\_ -> x) p == 0

mapVar :: (Num k, Eq k, Ord v1, Ord v2) => (v1 -> v2) -> Polynomial k v1 -> Polynomial k v2
mapVar f (Polynomial m) = normalize $ Polynomial $ Map.mapKeysWith (+) (mmMapVar f) m

mapCoeff :: (Eq k1, Num k1, Ord v) => (k -> k1) -> Polynomial k v -> Polynomial k1 v
mapCoeff f (Polynomial m) = normalize $ Polynomial $ Map.map f m

toMonic :: (Real r, Fractional r, Ord v) => Polynomial r v -> Polynomial r v
toMonic p
  | c == 0 = p
  | otherwise = mapCoeff (/c) p
  where
    (c,_) = leadingTerm grlex p

toZ :: (Real r, Ord v) => Polynomial r v -> Polynomial Integer v
toZ p = fromTerms [(numerator (c * fromInteger s), xs) | (c,xs) <- ts]
  where
    ts = [(toRational c, xs) | (c,xs) <- terms p]
    s = foldl' lcm  1 (map (denominator . fst) ts)

-- | Multivariate division algorithm
polyMDivMod
  :: forall k v. (Eq k, Fractional k, Ord v, Show v)
  => MonomialOrder v -> Polynomial k v -> [Polynomial k v] -> ([Polynomial k v], Polynomial k v)
polyMDivMod cmp p fs = go IM.empty p
  where
    ls = [(leadingTerm cmp f, f) | f <- fs]

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
          guard $ monomialDivisible h a
          let b = fromMonomial $ monomialDiv h a
          return (i, b, g - b * f)

-- | Multivariate division algorithm
reduce
  :: (Eq k, Fractional k, Ord v, Show v)
  => MonomialOrder v -> Polynomial k v -> [Polynomial k v] -> Polynomial k v
reduce cmp p fs = go p
  where
    ls = [(leadingTerm cmp f, f) | f <- fs]
    go g = if null xs then g else go (head xs)
      where
        ms = sortBy (flip cmp `on` snd) (terms g)
        xs = do
          (a,f) <- ls
          h <- ms
          guard $ monomialDivisible h a
          return (g - fromMonomial (monomialDiv h a) * f)

{--------------------------------------------------------------------
  Rendering
--------------------------------------------------------------------}

render
  :: (Eq k, Ord k, Num k, Ord v, RenderCoeff k, RenderVar v)
  => Polynomial k v -> String
render = renderWith renderVar

renderWith
  :: (Eq k, Ord k, Num k, Ord v, RenderCoeff k)
  => (Int -> v -> ShowS)
  -> Polynomial k v -> String
renderWith s2 p =
  case sortBy (flip grlex `on` snd) $ terms p of
    [] -> "0"
    (c,xs):ts -> f c xs ++ concat [if isNegativeCoeff c then " - " ++ (f (-c) xs) else " + " ++ f c xs | (c,xs) <- ts]
  where
    f c xs = (intercalate "*" ([renderCoeff 8 c "" | c /= 1 || null (mmToList xs)] ++ [g x e | (x,e) <- mmToList xs]))
    g x 1 = s2 8 x ""
    g x n = s2 9 x "" ++ "^" ++ show n

class RenderCoeff a where
  renderCoeff :: Int -> a -> ShowS
  isNegativeCoeff :: a -> Bool

instance RenderCoeff Integer where
  renderCoeff = showsPrec
  isNegativeCoeff = (0>)

instance RenderCoeff Rational where
  renderCoeff p r
    | denominator r == 1 = showsPrec p (numerator r)
    | otherwise = 
        showParen (p > ratioPrec) $
        showsPrec ratioPrec1 (numerator r) .
        showString "/" .
        showsPrec ratioPrec1 (denominator r)
    where
      ratioPrec, ratioPrec1 :: Int
      ratioPrec  = 7  -- Precedence of '/'
      ratioPrec1 = ratioPrec + 1
  isNegativeCoeff = (0>)

class RenderVar v where
  renderVar :: Int -> v -> ShowS

instance RenderVar Int where
  renderVar prec n = showChar 'x' . showsPrec 0 n

instance RenderVar () where
  renderVar prec n = showChar 'x'

{--------------------------------------------------------------------
  Univalent polynomials
--------------------------------------------------------------------}

-- | division of univalent polynomials
polyDiv :: (Eq k, Fractional k) => UPolynomial k -> UPolynomial k -> UPolynomial k
polyDiv f1 f2 = fst (polyDivMod f1 f2)

-- | division of univalent polynomials
polyMod :: (Eq k, Fractional k) => UPolynomial k -> UPolynomial k -> UPolynomial k
polyMod f1 f2 = snd (polyDivMod f1 f2)

-- | division of univalent polynomials
polyDivMod :: (Eq k, Fractional k) => UPolynomial k -> UPolynomial k -> (UPolynomial k, UPolynomial k)
polyDivMod f1 f2 = go f1
  where
    m2 = leadingTerm lex f2
    go 0 = (0,0)
    go f1
      | m1 `monomialDivisible` m2 =
          case go (f1 - fromMonomial (m1 `monomialDiv` m2) * f2) of
            (q,r) -> (q + fromMonomial (m1 `monomialDiv` m2), r)
      | otherwise = (0, f1)
      where
        m1 = leadingTerm lex f1

scaleLeadingTermToMonic :: (Eq k, Fractional k) => UPolynomial k -> UPolynomial k
scaleLeadingTermToMonic f = if c==0 then f else constant (1/c) * f
  where
    (c,_) = leadingTerm lex f

-- | GCD of univalent polynomials
polyGCD :: (Eq k, Fractional k) => UPolynomial k -> UPolynomial k -> UPolynomial k
polyGCD f1 0  = scaleLeadingTermToMonic f1
polyGCD f1 f2 = polyGCD f2 (f1 `polyMod` f2)

-- | LCM of univalent polynomials
polyLCM :: (Eq k, Fractional k) => UPolynomial k -> UPolynomial k -> UPolynomial k
polyLCM _ 0 = 0
polyLCM 0 _ = 0
polyLCM f1 f2 = scaleLeadingTermToMonic $ (f1 `polyMod` (polyGCD f1 f2)) * f2    

{--------------------------------------------------------------------
  Monomial
--------------------------------------------------------------------}

type Monomial k v = (k, MonicMonomial v)

monomialDegree :: Monomial k v -> Integer
monomialDegree (_,xs) = mmDegree xs

monomialProd :: (Num k, Ord v) => Monomial k v -> Monomial k v -> Monomial k v
monomialProd (c1,xs1) (c2,xs2) = (c1*c2, xs1 `mmProd` xs2)

monomialDivisible :: (Fractional k, Ord v) => Monomial k v -> Monomial k v -> Bool
monomialDivisible (c1,xs1) (c2,xs2) = mmDivisible xs1 xs2

monomialDiv :: (Fractional k, Ord v) => Monomial k v -> Monomial k v -> Monomial k v
monomialDiv (c1,xs1) (c2,xs2) = (c1 / c2, xs1 `mmDiv` xs2)

monomialDeriv :: (Eq k, Num k, Ord v) => Monomial k v -> v -> Monomial k v
monomialDeriv (c,xs) x =
  case mmDeriv xs x of
    (s,ys) -> (c * fromIntegral s, ys)

monomialIntegral :: (Eq k, Fractional k, Ord v) => Monomial k v -> v -> Monomial k v
monomialIntegral (c,xs) x =
  case mmIntegral xs x of
    (s,ys) -> (c * fromRational s, ys)

{--------------------------------------------------------------------
  Monic Monomial
--------------------------------------------------------------------}

-- 本当は変数の型に応じて type family で表現を変えたい

-- | Monic monomials
newtype MonicMonomial v = MonicMonomial (Map.Map v Integer)
  deriving (Eq, Ord)

instance (Ord v, Show v) => Show (MonicMonomial v) where
  showsPrec d m  = showParen (d > 10) $
    showString "mmFromList " . shows (mmToList m)

mmDegree :: MonicMonomial v -> Integer
mmDegree (MonicMonomial m) = sum $ Map.elems m

mmVar :: Ord v => v -> MonicMonomial v
mmVar x = MonicMonomial $ Map.singleton x 1

mmOne :: MonicMonomial v
mmOne = MonicMonomial $ Map.empty

mmFromList :: Ord v => [(v, Integer)] -> MonicMonomial v
mmFromList xs
  | any (\(x,e) -> 0>e) xs = error "mmFromList: negative exponent"
  | otherwise = MonicMonomial $ Map.fromListWith (+) [(x,e) | (x,e) <- xs, e > 0]

mmToList :: Ord v => MonicMonomial v -> [(v, Integer)]
mmToList (MonicMonomial m) = Map.toAscList m

mmToIntMap :: MonicMonomial Int -> IM.IntMap Integer
mmToIntMap (MonicMonomial m) = IM.fromDistinctAscList $ Map.toAscList m

mmProd :: Ord v => MonicMonomial v -> MonicMonomial v -> MonicMonomial v
mmProd (MonicMonomial xs1) (MonicMonomial xs2) = MonicMonomial $ Map.unionWith (+) xs1 xs2

mmDivisible :: Ord v => MonicMonomial v -> MonicMonomial v -> Bool
mmDivisible (MonicMonomial xs1) (MonicMonomial xs2) = Map.isSubmapOfBy (<=) xs2 xs1

mmDiv :: Ord v => MonicMonomial v -> MonicMonomial v -> MonicMonomial v
mmDiv (MonicMonomial xs1) (MonicMonomial xs2) = MonicMonomial $ Map.differenceWith f xs1 xs2
  where
    f m n
      | m <= n    = Nothing
      | otherwise = Just (m - n)

mmDeriv :: Ord v => MonicMonomial v -> v -> (Integer, MonicMonomial v)
mmDeriv (MonicMonomial xs) x
  | n==0      = (0, mmOne)
  | otherwise = (n, MonicMonomial $ Map.update f x xs)
  where
    n = Map.findWithDefault 0 x xs
    f m
      | m <= 1    = Nothing
      | otherwise = Just $! m - 1

mmIntegral :: Ord v => MonicMonomial v -> v -> (Rational, MonicMonomial v)
mmIntegral (MonicMonomial xs) x =
  (1 % fromIntegral (n + 1), MonicMonomial $ Map.insert x (n+1) xs)
  where
    n = Map.findWithDefault 0 x xs

mmLCM :: Ord v => MonicMonomial v -> MonicMonomial v -> MonicMonomial v
mmLCM (MonicMonomial m1) (MonicMonomial m2) = MonicMonomial $ Map.unionWith max m1 m2

mmGCD :: Ord v => MonicMonomial v -> MonicMonomial v -> MonicMonomial v
mmGCD (MonicMonomial m1) (MonicMonomial m2) = MonicMonomial $ Map.intersectionWith min m1 m2

mmMapVar :: (Ord v1, Ord v2) => (v1 -> v2) -> MonicMonomial v1 -> MonicMonomial v2
mmMapVar f (MonicMonomial m) = MonicMonomial $ Map.mapKeysWith (+) f m

{--------------------------------------------------------------------
  Monomial Order
--------------------------------------------------------------------}

type MonomialOrder v = MonicMonomial v -> MonicMonomial v -> Ordering

-- | Lexicographic order
lex :: Ord v => MonomialOrder v
lex xs1 xs2 = go (mmToList xs1) (mmToList xs2)
  where
    go [] [] = EQ
    go [] _  = LT -- = cmpare 0 n2
    go _ []  = GT -- = cmpare n1 0
    go ((x1,n1):xs1) ((x2,n2):xs2) =
      case compare x1 x2 of
        LT -> GT -- = compare n1 0
        GT -> LT -- = compare 0 n2
        EQ -> compare n1 n2 `mappend` go xs1 xs2

-- | Reverse lexicographic order
-- Note that revlex is NOT a monomial order.
revlex :: Ord v => MonicMonomial v -> MonicMonomial v -> Ordering
revlex xs1 xs2 = go (reverse (mmToList xs1)) (reverse (mmToList xs2))
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
grlex = (compare `on` mmDegree) `mappend` lex

-- | graded reverse lexicographic order
grevlex :: Ord v => MonomialOrder v
grevlex = (compare `on` mmDegree) `mappend` revlex
