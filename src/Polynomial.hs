{-# LANGUAGE ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses #-}

{-
メモ

Monomial order
http://en.wikipedia.org/wiki/Monomial_order

Gröbner basis
http://en.wikipedia.org/wiki/Gr%C3%B6bner_basis

グレブナー基底
http://d.hatena.ne.jp/keyword/%A5%B0%A5%EC%A5%D6%A5%CA%A1%BC%B4%F0%C4%EC

Gröbner Bases and Buchberger’s Algorithm
http://math.rice.edu/~cbruun/vigre/vigreHW6.pdf

Rubyでの実装
http://www.math.kobe-u.ac.jp/~kodama/tips-RubyPoly.html

HaskellではDoConに実装があり
http://www.haskell.org/docon/
GBasisモジュール
-}

module Polynomial
  (
  -- * Polynomial type
    Polynomial
  , UPolynomial

  -- * Conversion
  , var
  , constant
  , fromTerms
  , fromMonomial
  , terms

  -- * Query
  , leadingTerm
  , deg
  , coeff
  , lookupCoeff

  -- * Operations
  , deriv
  , eval
  , mapVar
  , mapCoeff
  , polyDiv
  , polyMod
  , polyDivMod
  , polyGCD
  , polyLCM

  -- * Monomial
  , Monomial
  , monomialDegree
  , monomialProd
  , monomialDivisible
  , monomialDiv
  , monomialDeriv

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
  , mmLCM
  , mmGCD
  , mmMapVar

  -- * Monomial order
  , MonomialOrder
  , lex
  , revlex
  , grlex
  , grevlex

  -- * Gröbner basis
  , buchberger
  , reduce
  , spolynomial
  , reduceGBase

  -- * Utility functions
  , showPoly
  ) where

import Prelude hiding (lex)
import Control.Monad
import Data.Function
import Data.List
import Data.Monoid
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.IntMap as IM
import Linear

{--------------------------------------------------------------------
  Polynomial type
--------------------------------------------------------------------}

newtype Polynomial k v = Polynomial (Map.Map (MonicMonomial v) k)
  deriving (Eq, Ord, Show)

-- | Univalent polynomials
type UPolynomial k = Polynomial k ()

instance (Eq k, Num k, Ord v) => Num (Polynomial k v) where
  Polynomial m1 + Polynomial m2 = normalize $ Polynomial $ Map.unionWith (+) m1 m2
  Polynomial m1 * Polynomial m2 = normalize $ Polynomial $ Map.fromListWith (+)
      [ (xs1 `mmProd` xs2, c1*c2)
      | (xs1,c1) <- Map.toList m1, (xs2,c2) <- Map.toList m2
      ]
  negate (Polynomial m) = Polynomial $ Map.map negate m
  abs x = x    -- OK?
  signum x = 1 -- OK?
  fromInteger x = constant (fromInteger x)

instance (Eq k, Num k, Ord v) => Module k (Polynomial k v) where
  k .*. p = constant k * p
  p .+. q = p + q
  lzero = 0

instance (Eq k, Fractional k, Ord v) => Linear k (Polynomial k v)

normalize :: (Eq k, Num k, Ord v) => Polynomial k v -> Polynomial k v
normalize (Polynomial m) = Polynomial (Map.filter (0/=) m)

var :: (Eq k, Num k, Ord v) => v -> Polynomial k v
var x = fromMonomial (1, mmVar x)

constant :: (Eq k, Num k, Ord v) => k -> Polynomial k v
constant c = fromMonomial (c, mmOne)

fromTerms :: (Eq k, Num k, Ord v) => [Monomial k v] -> Polynomial k v
fromTerms = normalize . Polynomial . Map.fromListWith (+) . map (\(c,xs) -> (xs,c))

fromMonomial :: (Eq k, Num k, Ord v) => Monomial k v -> Polynomial k v
fromMonomial (c,xs) = normalize $ Polynomial $ Map.singleton xs c

terms :: Polynomial k v -> [Monomial k v]
terms (Polynomial m) = [(c,xs) | (xs,c) <- Map.toList m]

leadingTerm :: (Eq k, Num k, Ord v) => MonomialOrder v -> Polynomial k v -> Monomial k v
leadingTerm cmp p =
  case terms p of
    [] -> (0, mmOne) -- should be error?
    ms -> maximumBy (cmp `on` snd) ms

deg :: Polynomial k v -> Integer
deg = maximum . (0:) . map monomialDegree . terms

coeff :: (Num k, Ord v) => MonicMonomial v -> Polynomial k v -> k
coeff xs (Polynomial m) = Map.findWithDefault 0 xs m

lookupCoeff :: Ord v => MonicMonomial v -> Polynomial k v -> Maybe k
lookupCoeff xs (Polynomial m) = Map.lookup xs m

deriv :: (Eq k, Num k, Ord v) => Polynomial k v -> v -> Polynomial k v
deriv p x = sum [fromMonomial (monomialDeriv m x) | m <- terms p]

eval :: (Num k, Ord v) => (v -> k) -> Polynomial k v -> k
eval env p = sum [c * product [(env x) ^ n | (x,n) <- mmToList xs] | (c,xs) <- terms p]

mapVar :: (Num k, Eq k, Ord v1, Ord v2) => (v1 -> v2) -> Polynomial k v1 -> Polynomial k v2
mapVar f (Polynomial m) = normalize $ Polynomial $ Map.mapKeysWith (+) (mmMapVar f) m

mapCoeff :: (Eq k1, Num k1, Ord v) => (k -> k1) -> Polynomial k v -> Polynomial k1 v
mapCoeff f (Polynomial m) = normalize $ Polynomial $ Map.map f m

showPoly :: (Eq k, Ord k, Num k, Show k, Ord v, Show v) => Polynomial k v -> String
showPoly p = intercalate " + " [f c xs | (c,xs) <- sortBy (flip grlex `on` snd) $ terms p]
  where
    f c xs = (intercalate "*" ([showsPrec 8 c "" | c /= 1 || null (mmToList xs)] ++ [g x n | (x,n) <- mmToList xs]))
    g x 1 = "x" ++ show x
    g x n = "x" ++ show x ++ "^" ++ show n

{--------------------------------------------------------------------
  Monomial
--------------------------------------------------------------------}

polyDiv :: (Eq k, Fractional k) => UPolynomial k -> UPolynomial k -> UPolynomial k
polyDiv f1 f2 = fst (polyDivMod f1 f2)

polyMod :: (Eq k, Fractional k) => UPolynomial k -> UPolynomial k -> UPolynomial k
polyMod f1 f2 = snd (polyDivMod f1 f2)

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

polyGCD :: (Eq k, Fractional k) => UPolynomial k -> UPolynomial k -> UPolynomial k
polyGCD f1 0  = scaleLeadingTermToMonic f1
polyGCD f1 f2 = polyGCD f2 (f1 `polyMod` f2)

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

{--------------------------------------------------------------------
  Monic Monomial
--------------------------------------------------------------------}

-- 本当は変数の型に応じて type family で表現を変えたい

newtype MonicMonomial v = MonicMonomial (Map.Map v Integer)
  deriving (Eq, Ord, Show)

mmDegree :: MonicMonomial v -> Integer
mmDegree (MonicMonomial m) = sum $ Map.elems m

mmVar :: Ord v => v -> MonicMonomial v
mmVar x = MonicMonomial $ Map.singleton x 1

mmOne :: MonicMonomial v
mmOne = MonicMonomial $ Map.empty

mmFromList :: Ord v => [(v, Integer)] -> MonicMonomial v
mmFromList xs = MonicMonomial $ Map.fromListWith (+) [(x, n) | (x,n) <- xs, n > 0]

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

{--------------------------------------------------------------------
  Gröbner basis
--------------------------------------------------------------------}

-- | Multivariate division algorithm
reduce  :: (Eq k, Fractional k, Ord v) => MonomialOrder v -> Polynomial k v -> [Polynomial k v] -> Polynomial k v
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

spolynomial :: (Eq k, Fractional k, Ord v) => MonomialOrder v -> Polynomial k v -> Polynomial k v -> Polynomial k v
spolynomial cmp f g =
      fromMonomial ((1,xs) `monomialDiv` (c1,xs1)) * f
    - fromMonomial ((1,xs) `monomialDiv` (c2,xs2)) * g
  where
    xs = mmLCM xs1 xs2
    (c1, xs1) = leadingTerm cmp f
    (c2, xs2) = leadingTerm cmp g

buchberger :: forall k v. (Eq k, Fractional k, Ord k, Ord v) => MonomialOrder v -> [Polynomial k v] -> [Polynomial k v]
buchberger cmp fs = reduceGBase cmp $ go fs (pairs fs)
  where  
    go :: [Polynomial k v] -> [(Polynomial k v, Polynomial k v)] -> [Polynomial k v]
    go gs [] = gs
    go gs ((fi,fj):ps)
      | r == 0    = go gs ps
      | otherwise = go (r:gs) ([(r,g) | g <- gs] ++ ps)
      where
        spoly = spolynomial cmp fi fj
        r = reduce cmp spoly gs

reduceGBase :: forall k v. (Eq k, Ord k, Fractional k, Ord v) => MonomialOrder v -> [Polynomial k v] -> [Polynomial k v]
reduceGBase cmp ps = Set.toList $ Set.fromList $ go ps []
  where
    go [] qs = qs
    go (p:ps) qs
      | q == 0    = go ps qs
      | otherwise = go ps (constant (1/c) * q : qs)
      where
        q = reduce cmp p (ps++qs)
        (c,_) = leadingTerm cmp q

{--------------------------------------------------------------------
  Utilities
--------------------------------------------------------------------}

pairs :: [a] -> [(a,a)]
pairs [] = []
pairs (x:xs) = [(x,y) | y <- xs] ++ pairs xs
