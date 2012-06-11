{-# LANGUAGE ScopedTypeVariables #-}

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
    Var
  , Polynomial

  -- * Conversion
  , var
  , constant
  , fromMonomials
  , fromMonomial
  , terms

  -- * Query
  , leadingTerm
  , deg

  -- * Operations
  , deriv

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
  , mmDegree
  , mmProd
  , mmDivisible
  , mmDiv
  , mmDeriv
  , mmLCM
  , mmGCD

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

{--------------------------------------------------------------------
  Polynomial type
--------------------------------------------------------------------}

type Var = Int

newtype Polynomial k = Polynomial (Map.Map MonicMonomial k)
  deriving (Eq, Ord, Show)

instance (Eq k, Num k) => Num (Polynomial k) where
  Polynomial m1 + Polynomial m2 = normalize $ Polynomial $ Map.unionWith (+) m1 m2
  Polynomial m1 * Polynomial m2 = normalize $ Polynomial $ Map.fromListWith (+)
      [ (xs1 `mmProd` xs2, c1*c2)
      | (xs1,c1) <- Map.toList m1, (xs2,c2) <- Map.toList m2
      ]
  negate (Polynomial m) = Polynomial $ Map.map negate m
  abs x = x    -- OK?
  signum x = 1 -- OK?
  fromInteger x = constant (fromInteger x)

normalize :: (Eq k, Num k) => Polynomial k -> Polynomial k
normalize (Polynomial m) = Polynomial (Map.filter (0/=) m)

var :: (Eq k, Num k) => Var -> Polynomial k
var x = fromMonomial (1, mmVar x)

constant :: (Eq k, Num k) => k -> Polynomial k
constant c = fromMonomial (c, mmOne)

fromMonomials :: (Eq k, Num k) => [Monomial k] -> Polynomial k
fromMonomials = normalize . Polynomial . Map.fromListWith (+) . map (\(c,xs) -> (xs,c))

fromMonomial :: (Eq k, Num k) => Monomial k -> Polynomial k
fromMonomial (c,xs) = normalize $ Polynomial $ Map.singleton xs c

terms :: Polynomial k -> [Monomial k]
terms (Polynomial m) = [(c,xs) | (xs,c) <- Map.toList m]

leadingTerm :: (Eq k, Num k) => MonomialOrder -> Polynomial k -> Monomial k
leadingTerm cmp p =
  case terms p of
    [] -> (0, mmOne) -- should be error?
    ms -> maximumBy (cmp `on` snd) ms

deg :: Polynomial k -> Integer
deg = maximum . map monomialDegree . terms

deriv :: (Eq k, Num k) => Polynomial k -> Var -> Polynomial k
deriv p x = sum [fromMonomial (monomialDeriv m x) | m <- terms p]

showPoly :: (Eq k, Ord k, Num k, Show k) => Polynomial k -> String
showPoly p = intercalate " + " [f c xs | (c,xs) <- sortBy (flip grlex `on` snd) $ terms p]
  where
    f c xs = (intercalate "*" ([showsPrec 8 c "" | c /= 1 || null (mmToList xs)] ++ [g x n | (x,n) <- mmToList xs]))
    g x 1 = "x" ++ show x
    g x n = "x" ++ show x ++ "^" ++ show n

{--------------------------------------------------------------------
  Monomial
--------------------------------------------------------------------}

type Monomial k = (k, MonicMonomial)

monomialDegree :: Monomial k -> Integer
monomialDegree (_,xs) = mmDegree xs

monomialProd :: Num k => Monomial k -> Monomial k -> Monomial k
monomialProd (c1,xs1) (c2,xs2) = (c1*c2, xs1 `mmProd` xs2)

monomialDivisible :: Fractional k => Monomial k -> Monomial k -> Bool
monomialDivisible (c1,xs1) (c2,xs2) = mmDivisible xs1 xs2

monomialDiv :: Fractional k => Monomial k -> Monomial k -> Monomial k
monomialDiv (c1,xs1) (c2,xs2) = (c1 / c2, xs1 `mmDiv` xs2)

monomialDeriv :: (Eq k, Num k) => Monomial k -> Var -> Monomial k
monomialDeriv (c,xs) x =
  case mmDeriv xs x of
    (s,ys) -> (c * fromIntegral s, ys)

{--------------------------------------------------------------------
  Monic Monomial
--------------------------------------------------------------------}

type MonicMonomial = IM.IntMap Integer

mmDegree :: MonicMonomial -> Integer
mmDegree = sum . IM.elems 

mmVar :: Var -> MonicMonomial
mmVar x = IM.singleton x 1

mmOne :: MonicMonomial
mmOne = IM.empty

mmFromList :: [(Var, Integer)] -> MonicMonomial
mmFromList xs = IM.fromList [(x, n) | (x,n) <- xs, n /= 0]

mmToList :: MonicMonomial -> [(Var, Integer)]
mmToList = IM.toAscList

mmProd :: MonicMonomial -> MonicMonomial -> MonicMonomial
mmProd xs1 xs2 = IM.unionWith (+) xs1 xs2

mmDivisible :: MonicMonomial -> MonicMonomial -> Bool
mmDivisible xs1 xs2 = IM.isSubmapOfBy (<=) xs2 xs1

mmDiv :: MonicMonomial -> MonicMonomial -> MonicMonomial
mmDiv xs1 xs2 = IM.differenceWith f xs1 xs2
  where
    f m n
      | m <= n    = Nothing
      | otherwise = Just (m - n)

mmDeriv :: MonicMonomial -> Var -> (Integer, MonicMonomial)
mmDeriv xs x
  | n==0      = (0, IM.empty)
  | otherwise = (n, IM.update f x xs)
  where
    n = IM.findWithDefault 0 x xs
    f m
      | m <= 1    = Nothing
      | otherwise = Just $! m - 1

mmLCM :: MonicMonomial -> MonicMonomial -> MonicMonomial
mmLCM = IM.unionWith max

mmGCD :: MonicMonomial -> MonicMonomial -> MonicMonomial
mmGCD m1 m2 = IM.filter (0/=) $ IM.intersectionWith min m1 m2

{--------------------------------------------------------------------
  Monomial Order
--------------------------------------------------------------------}

type MonomialOrder = MonicMonomial -> MonicMonomial -> Ordering

-- | Lexicographic order
lex :: MonomialOrder
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
revlex :: MonicMonomial -> MonicMonomial -> Ordering
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
grlex :: MonomialOrder
grlex = (compare `on` mmDegree) `mappend` lex

-- | graded reverse lexicographic order
grevlex :: MonomialOrder
grevlex = (compare `on` mmDegree) `mappend` revlex

{--------------------------------------------------------------------
  Gröbner basis
--------------------------------------------------------------------}

-- | Multivariate division algorithm
reduce  :: (Eq k, Fractional k) => MonomialOrder -> Polynomial k -> [Polynomial k] -> Polynomial k
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

spolynomial :: (Eq k, Fractional k) => MonomialOrder -> Polynomial k -> Polynomial k -> Polynomial k
spolynomial cmp f g =
      fromMonomial ((1,xs) `monomialDiv` (c1,xs1)) * f
    - fromMonomial ((1,xs) `monomialDiv` (c2,xs2)) * g
  where
    xs = mmLCM xs1 xs2
    (c1, xs1) = leadingTerm cmp f
    (c2, xs2) = leadingTerm cmp g

buchberger :: forall k. (Eq k, Fractional k, Ord k) => MonomialOrder -> [Polynomial k] -> [Polynomial k]
buchberger cmp fs = reduceGBase cmp $ go fs (pairs fs)
  where  
    go :: [Polynomial k] -> [(Polynomial k, Polynomial k)] -> [Polynomial k]
    go gs [] = gs
    go gs ((fi,fj):ps)
      | r == 0    = go gs ps
      | otherwise = go (r:gs) ([(r,g) | g <- gs] ++ ps)
      where
        spoly = spolynomial cmp fi fj
        r = reduce cmp spoly gs

reduceGBase :: forall k. (Eq k, Ord k, Fractional k) => MonomialOrder -> [Polynomial k] -> [Polynomial k]
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
