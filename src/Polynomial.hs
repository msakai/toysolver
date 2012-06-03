{-# LANGUAGE ScopedTypeVariables #-}

{-
メモ

Gröbner basis
http://en.wikipedia.org/wiki/Gr%C3%B6bner_basis

グレブナー基底
http://d.hatena.ne.jp/keyword/%A5%B0%A5%EC%A5%D6%A5%CA%A1%BC%B4%F0%C4%EC

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
  , MonicMonomial
  , Monomial
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
  , monomialDegree
  , monicMonomialDegree

  -- * Operations
  , deriv

  -- * Monomial order
  , MonomialOrder
  , lex
  , grlex
  , grevlex

  -- * Gröbner basis
  , buchberger

  -- * Multivariate division algorithm
  , reduce

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
import qualified Data.IntMultiSet as IMS

{--------------------------------------------------------------------
  Polynomial type
--------------------------------------------------------------------}

type Var = Int
type MonicMonomial = IMS.IntMultiSet
type Monomial k = (k, MonicMonomial)

newtype Polynomial k = Polynomial (Map.Map MonicMonomial k)
  deriving (Eq, Ord, Show)

instance (Eq k, Num k) => Num (Polynomial k) where
  Polynomial m1 + Polynomial m2 = normalize $ Polynomial $ Map.unionWith (+) m1 m2
  Polynomial m1 * Polynomial m2 = normalize $ Polynomial $ Map.fromListWith (+)
      [ (xs1 `IMS.union` xs2, c1*c2)
      | (xs1,c1) <- Map.toList m1, (xs2,c2) <- Map.toList m2
      ]
  negate (Polynomial m) = Polynomial $ Map.map negate m
  abs x = x    -- OK?
  signum x = 1 -- OK?
  fromInteger x = normalize $ Polynomial $ Map.singleton IMS.empty (fromInteger x)

normalize :: (Eq k, Num k) => Polynomial k -> Polynomial k
normalize (Polynomial m) = Polynomial (Map.filter (0/=) m)

var :: (Eq k, Num k) => Var -> Polynomial k
var x = Polynomial (Map.singleton (IMS.singleton x) 1)

constant :: (Eq k, Num k) => k -> Polynomial k
constant c = normalize $ Polynomial (Map.singleton IMS.empty c)

fromMonomials :: (Eq k, Num k) => [Monomial k] -> Polynomial k
fromMonomials = normalize . Polynomial . Map.fromListWith (+) . map (\(c,xs) -> (xs,c))

fromMonomial :: (Eq k, Num k) => Monomial k -> Polynomial k
fromMonomial (c,xs) = normalize $ Polynomial $ Map.singleton xs c

terms :: Polynomial k -> [Monomial k]
terms (Polynomial m) = [(c,xs) | (xs,c) <- Map.toList m]

leadingTerm :: (Eq k, Num k) => MonomialOrder -> Polynomial k -> Monomial k
leadingTerm cmp p =
  case terms p of
    [] -> (0, IMS.empty) -- should be error?
    ms -> maximumBy (cmp `on` snd) ms

deg :: Polynomial k -> Integer
deg = maximum . map monomialDegree . terms

monomialDegree :: Monomial k -> Integer
monomialDegree (_,xs) = monicMonomialDegree xs

monicMonomialDegree :: MonicMonomial -> Integer
monicMonomialDegree xs = fromIntegral $ IMS.size xs

deriv :: (Eq k, Num k) => Polynomial k -> Var -> Polynomial k
deriv p x = sum $ do
  (c,xs) <- terms p
  let n = IMS.occur x xs
  if n == 0
    then return 0
    else return $ fromMonomial (c * fromIntegral n, IMS.delete x xs)

showPoly :: (Eq k, Ord k, Num k, Show k) => Polynomial k -> String
showPoly p = intercalate " + " [f c xs | (c,xs) <- sortBy (flip grlex `on` snd) $ terms p]
  where
    f c xs = (intercalate "*" ([showsPrec 8 c "" | c /= 1] ++ [g x n | (x,n) <- IMS.toOccurList xs]))
    g x 1 = "x" ++ show x
    g x n = "x" ++ show x ++ "^" ++ show n


type MonomialOrder = MonicMonomial -> MonicMonomial -> Ordering

lex :: MonomialOrder
lex xs1 xs2 = go (IMS.toAscOccurList xs1) (IMS.toAscOccurList xs2)
  where
    go [] [] = EQ
    go [] _ = LT
    go _ [] = GT
    go ((x1,n1):xs1) ((x2,n2):xs2) =
      case compare x1 x2 of
        LT -> GT -- = compare n1 0
        GT -> LT -- = compare 0 n2
        EQ -> compare n1 n2 `mappend` go xs1 xs2

-- http://en.wikipedia.org/wiki/Monomial_order
test_lex = sortBy lex [a,b,c,d] == [b,a,d,c]
  where
    x = 1
    y = 2
    z = 3
    a = IMS.fromOccurList [(x,1),(y,2),(z,1)]
    b = IMS.fromOccurList [(z,2)]
    c = IMS.fromOccurList [(x,3)]
    d = IMS.fromOccurList [(x,2),(z,2)]

revlex :: MonomialOrder
revlex xs1 xs2 = go (reverse (IMS.toAscOccurList xs1)) (reverse (IMS.toAscOccurList xs2))
  where
    go [] [] = EQ
    go [] _ = GT
    go _ [] = LT
    go ((x1,n1):xs1) ((x2,n2):xs2) =
      case compare x1 x2 of
        LT -> LT -- = compare 0 n1
        GT -> GT -- = compare n2 0
        EQ -> compare n2 n1 `mappend` go xs1 xs2

grlex :: MonomialOrder
grlex = (compare `on` monicMonomialDegree) `mappend` lex

-- http://en.wikipedia.org/wiki/Monomial_order
test_grlex = sortBy grlex [a,b,c,d] == [b,c,a,d]
  where
    x = 1
    y = 2
    z = 3
    a = IMS.fromOccurList [(x,1),(y,2),(z,1)]
    b = IMS.fromOccurList [(z,2)]
    c = IMS.fromOccurList [(x,3)]
    d = IMS.fromOccurList [(x,2),(z,2)]

grevlex :: MonomialOrder
grevlex = (compare `on` monicMonomialDegree) `mappend` revlex

-- http://en.wikipedia.org/wiki/Monomial_order
test_grevlex = sortBy grevlex [a,b,c,d] == [b,c,d,a]
  where
    x = 1
    y = 2
    z = 3
    a = IMS.fromOccurList [(x,1),(y,2),(z,1)]
    b = IMS.fromOccurList [(z,2)]
    c = IMS.fromOccurList [(x,3)]
    d = IMS.fromOccurList [(x,2),(z,2)]

lcmMonicMonomial :: MonicMonomial -> MonicMonomial -> MonicMonomial
lcmMonicMonomial = IMS.maxUnion

-- lcm (x1^2 * x2^4) (x1^3 * x2^1) = x1^3 * x2^4
test_lcmMonicMonomial = lcmMonicMonomial p1 p2 == IMS.fromOccurList [(1,3),(2,4)]
  where
    p1 = IMS.fromOccurList [(1,2),(2,4)]
    p2 = IMS.fromOccurList [(1,3),(2,1)]

monicMonomialDivisible :: MonicMonomial -> MonicMonomial -> Bool
monicMonomialDivisible xs1 xs2 = xs2 `IMS.isSubsetOf` xs1

monicMonomialDiv :: MonicMonomial -> MonicMonomial -> MonicMonomial
monicMonomialDiv xs1 xs2 = xs1 `IMS.difference` xs2

monomialDivisible :: Fractional k => Monomial k -> Monomial k -> Bool
monomialDivisible (c1,xs1) (c2,xs2) = monicMonomialDivisible xs1 xs2

monomialDiv :: Fractional k => Monomial k -> Monomial k -> Monomial k
monomialDiv (c1,xs1) (c2,xs2) = (c1 / c2, xs1 `monicMonomialDiv` xs2)

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

spolynomial :: Fractional k => MonomialOrder -> Polynomial k -> Polynomial k -> Polynomial k
spolynomial cmp f g =
      fromMonomial ((1,xs) `monomialDiv` (c1,xs1)) * f
    - fromMonomial ((1,xs) `monomialDiv` (c2,xs2)) * g
  where
    xs = lcmMonicMonomial xs1 xs2
    (c1, xs1) = leadingTerm cmp f
    (c2, xs2) = leadingTerm cmp g

-- http://math.rice.edu/~cbruun/vigre/vigreHW6.pdf
test_spolynomial = spolynomial grlex f g == - x^3*y^3 - constant (1/3) * y^3 + x^2
  where
    x = var 1
    y = var 2
    f, g :: Polynomial Rational
    f = x^3*y^2 - x^2*y^3 + x
    g = 3*x^4*y + y^2

buchberger :: forall k. (Eq k, Fractional k, Ord k) => MonomialOrder -> [Polynomial k] -> [Polynomial k]
buchberger cmp fs = (Set.toList . go . Set.fromList) fs
  where  
    go :: Set.Set (Polynomial k) -> Set.Set (Polynomial k)
    go fs = if fs2 `Set.isSubsetOf` fs
            then fs
            else go (fs `Set.union` fs2)
      where
        fs2 = Set.fromList $ do
          (fi,fj) <- pairs (Set.toList fs)
          guard $ fi /= fj
          let spoly = spolynomial cmp fi fj
          let p = reduce cmp spoly (Set.toList fs)
          guard $ p /= 0
          return p

test_buchberger1 = buchberger lex [x^2-y, x^3-z]
  where
    x :: Polynomial Rational
    x = var 1
    y = var 2
    z = var 3

test_buchberger2 = buchberger lex [x^3-2*x*y, x^2*y-2*y^2+x]
  where
    x :: Polynomial Rational
    x = var 1
    y = var 2

-- http://www.iisdavinci.it/jeometry/buchberger.html
test_buchberger3 = buchberger lex [x^2+2*x*y^2, x*y+2*y^3-1]
  where
    x :: Polynomial Rational
    x = var 1
    y = var 2

-- http://www.orcca.on.ca/~reid/NewWeb/DetResDes/node4.html
test_buchberger4 = buchberger grlex [x^2+y*z-2, x*z*y^2-3, x*y+z^2-5]
  where
    x :: Polynomial Rational
    x = var 1
    y = var 2
    z = var 3

pairs :: [a] -> [(a,a)]
pairs [] = []
pairs (x:xs) = [(x,y) | y <- xs] ++ pairs xs
