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

  -- * Constructions
  , var
  , fromMonomials
  , fromMonomial

  -- * Query
  , terms
  , leadingTerm
  , deg
  , monomialDegree
  , monicMonomialDegree

  -- * Monomial order
  , MonomialOrder
  , lex
  , grlex

  -- * Gröbner basis
  , buchberger

  -- * Multivariate division algorithm
  , multivariateDivision

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



showPoly :: (Eq k, Ord k, Num k, Show k) => Polynomial k -> String
showPoly p = intercalate " " [f c xs | (c,xs) <- sortBy (flip grlex `on` snd) $ terms p]
  where
    f c xs = (if c >= 0 then "+" else "") ++ 
             (intercalate "*" ([show c | c /= 1] ++ [g x n | (x,n) <- IMS.toOccurList xs]))
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

test_lex_1 = lex (IMS.singleton 1) (IMS.singleton 2) == GT
test_lex_2 = lex (IMS.fromOccurList [(1,1),(2,1)]) (IMS.fromOccurList [(1,1),(2,2)]) == LT
test_lex_3 = lex (IMS.fromOccurList [(2,2)]) (IMS.fromOccurList [(1,1),(2,1)]) == LT

grlex :: MonomialOrder
grlex = (compare `on` monicMonomialDegree) `mappend` lex


lcmMonicMonomial :: MonicMonomial -> MonicMonomial -> MonicMonomial
lcmMonicMonomial = IMS.maxUnion

-- lcm (x1^2 * x2^4) (x1^3 * x2^1) = x1^3 * x2^4
test_lcmMonicMonomial = lcmMonicMonomial p1 p2 == IMS.fromOccurList [(1,3),(2,4)]
  where
    p1 = IMS.fromOccurList [(1,2),(2,4)]
    p2 = IMS.fromOccurList [(1,3),(2,1)]

lcmMonomial :: (Eq k, Integral k) => Monomial k -> Monomial k -> Monomial k
lcmMonomial (c1,xs1) (c2,xs2) = (lcm c1 c2, lcmMonicMonomial xs1 xs2)

monomialDivisible :: (Eq k, Integral k) => Monomial k -> Monomial k -> Bool
monomialDivisible (c1,xs1) (c2,xs2) = c1 `mod` c2 == 0 && xs2 `IMS.isSubsetOf` xs1

monomialDiv :: (Eq k, Integral k) => Monomial k -> Monomial k -> Monomial k
monomialDiv (c1,xs1) (c2,xs2) = (c1 `div` c2, xs1 `IMS.difference` xs2)

multivariateDivision  :: (Eq k, Integral k) => MonomialOrder -> Polynomial k -> [Polynomial k] -> Polynomial k
multivariateDivision cmp p fs = go p
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


buchberger :: forall k. (Eq k, Integral k) => MonomialOrder -> [Polynomial k] -> [Polynomial k]
buchberger cmp fs = (Set.toList . go . Set.fromList) fs
  where  
    go :: Set.Set (Polynomial k) -> Set.Set (Polynomial k)
    go fs = if fs2 `Set.isSubsetOf` fs
            then fs
            else go (fs `Set.union` fs2)
      where
        fs2 = Set.fromList $ do
          let fs' = [(leadingTerm cmp f, f) | f <- Set.toList fs]
          ((gi,fi),(gj,fj)) <- pairs fs'
          guard $ fi /= fj
          let aij = lcmMonomial gi gj
          let spoly = fromMonomial (aij `monomialDiv` gi) * fi - fromMonomial (aij `monomialDiv` gj) * fj
          let p = multivariateDivision cmp spoly (Set.toList fs)
          guard $ p /= 0
          return p

test_buchberger1 = buchberger lex [x^2-y, x^3-z]
  where
    x = var 1
    y = var 2
    z = var 3

test_buchberger2 = buchberger lex [x^3-2*x*y, x^2*y-2*y^2+x]
  where
    x = var 1
    y = var 2

-- http://www.iisdavinci.it/jeometry/buchberger.html
test_buchberger3 = buchberger lex [x^2+2*x*y^2, x*y+2*y^3-1]
  where
    x = var 1
    y = var 2

-- http://www.orcca.on.ca/~reid/NewWeb/DetResDes/node4.html
test_buchberger4 = buchberger grlex [x^2+y*z-2, x*z*y^2-3, x*y+z^2-5]
  where
    x = var 1
    y = var 2
    z = var 3

pairs :: [a] -> [(a,a)]
pairs [] = []
pairs (x:xs) = [(x,y) | y <- xs] ++ pairs xs
