{-# LANGUAGE BangPatterns #-}
-- http://en.wikipedia.org/wiki/Polynomial_factorization
-- Kronecker's method
module Data.Polynomial.FactorZ
  ( factor
  ) where

import Data.List
import Data.Numbers.Primes (primes)
import Data.Polynomial
import qualified Data.Polynomial.Lagrange as Lagrange
import Util (isInteger)

factor :: UPolynomial Integer -> [UPolynomial Integer]
factor p = normalize $ factor' p

normalize :: [UPolynomial Integer] -> [UPolynomial Integer]
normalize ps = [constant c | let c = product $ map fst xs, c /= 1] ++ sort (map snd xs)
  where
    xs = map f ps

    f :: UPolynomial Integer -> (Integer, UPolynomial Integer)
    f q = case [c | (c,_) <- terms q] of
            [] -> (1,q)
            (c:cs) ->
              let d :: Integer
                  d = foldl' gcd c cs
                  q2 = mapCoeff (`div` d) q
              in if fst (leadingTerm grlex q2) < 0
                 then (-d,q2)
                 else (d,q2)

factor' :: UPolynomial Integer -> [UPolynomial Integer]
factor' 0 = [0]
factor' 1 = []
factor' p | deg p == 0 = [p]
factor' p =
  case factor2 p of
    Nothing -> [p]
    Just qs -> concatMap factor' qs

factor2 :: UPolynomial Integer -> Maybe [UPolynomial Integer]
factor2 p | p == var X = Nothing
factor2 p =
  case find (\(_,yi) -> yi==0) vs of
    Just (xi,_) ->
      let q1 = x - constant xi
          q2 = p' `polyDiv` mapCoeff fromInteger q1
      in Just [q1, toZ q2]
    Nothing ->
      let qs = map Lagrange.interpolation $
                  sequence [[(fromInteger xi, fromInteger z) | z <- factors yi] | (xi,yi) <- vs]
          zs = [ (q1,q2)
               | q1 <- qs, deg q1 > 0, isUPolyZ q1
               , let (q2,r) = p' `polyDivMod` q1
               , r == 0, deg q2 > 0, isUPolyZ q2
               ]
      in case zs of
           [] -> Nothing
           (q1,q2):_ -> Just [toZ q1, toZ q2]
  where
    n = (deg p `div` 2)
    xs = take (fromIntegral n + 1) xvalues
    vs = [(x, eval (\X -> x) p) | x <- xs]
    x = var X
    p' :: UPolynomial Rational
    p' = mapCoeff fromInteger p

isUPolyZ :: UPolynomial Rational -> Bool
isUPolyZ p = and [isInteger c | (c,_) <- terms p]

-- [0, 1, -1, 2, -2, 3, -3 ..]
xvalues :: [Integer]
xvalues = 0 : interleave [1,2..] [-1,-2..]

interleave :: [a] -> [a] -> [a]
interleave xs [] = xs
interleave [] ys     = ys
interleave (x:xs) ys = x : interleave ys xs

factors :: Integer -> [Integer]
factors 0 = []
factors x = xs ++ map negate xs
  where
    ps = primeFactors (abs x)
    xs = map product $ sequence [[p^i | i <- [0..n]] | (p,n) <- ps]

primeFactors :: Integer -> [(Integer,Integer)]
primeFactors 0 = []
primeFactors n = f primes n
  where
    f :: [Integer] -> Integer -> [(Integer,Integer)]
    f !_ 1 = []
    f (p:ps) n
      | p*p > n   = [(n,1)]
      | otherwise =
          case g p n of
            (m,n') -> [(p,m) | m /= 0] ++ f ps n'

    g :: Integer -> Integer -> (Integer, Integer)
    g p = go 0
      where
        go !m !n
          | n `mod` p == 0 = go (m+1) (n `div` p)
          | otherwise = (m, n)
          