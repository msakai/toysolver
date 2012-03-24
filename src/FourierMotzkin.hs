{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  FourierMotzkin
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Naïve implementation of Fourier-Motzkin Variable Elimination
-- 
-- see http://users.cecs.anu.edu.au/~michaeln/pubs/arithmetic-dps.pdf for detail
--
-----------------------------------------------------------------------------
module FourierMotzkin
    ( module Expr
    , module Formula
    , module LA
    , Lit (..)
    , eliminateQuantifiers
    , solve

    -- FIXME
    , termR
    , Rat
    , collectBounds
    , boundConditions
    , evalBounds
    , simplify
    , constraintsToDNF
    ) where

import Control.Monad
import Data.List
import Data.Maybe
import Data.Ratio
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS

import Expr
import Formula
import LA
import Interval

-- ---------------------------------------------------------------------------

type LCZ = LC Integer

-- | (t,c) represents t/c, and c must be >0.
type Rat = (LCZ, Integer)

evalRat :: Model Rational -> Rat -> Rational
evalRat model (lc, c1) = lift1LC 1 (model IM.!) (mapLC fromIntegral lc) / (fromIntegral c1)

-- | Literal
data Lit = Nonneg LCZ | Pos LCZ deriving (Show, Eq, Ord)

instance Variables Lit where
  vars (Pos t) = vars t
  vars (Nonneg t) = vars t

instance Complement Lit where
  notF (Pos t) = Nonneg (lnegate t)
  notF (Nonneg t) = Pos (lnegate t)

-- 制約集合の単純化
-- It returns Nothing when a inconsistency is detected.
simplify :: [Lit] -> Maybe [Lit]
simplify = fmap concat . mapM f
  where
    f :: Lit -> Maybe [Lit]
    f lit@(Pos lc) =
      case asConst lc of
        Just x -> guard (x > 0) >> return []
        Nothing -> return [lit]
    f lit@(Nonneg lc) =
      case asConst lc of
        Just x -> guard (x >= 0) >> return []
        Nothing -> return [lit]

-- ---------------------------------------------------------------------------

atomR :: RelOp -> Expr Rational -> Expr Rational -> Maybe (DNF Lit)
atomR op a b = do
  a' <- termR a
  b' <- termR b
  return $ case op of
    Le -> DNF [[a' `leR` b']]
    Lt -> DNF [[a' `ltR` b']]
    Ge -> DNF [[a' `geR` b']]
    Gt -> DNF [[a' `gtR` b']]
    Eql -> DNF [[a' `leR` b', a' `geR` b']]
    NEq -> DNF [[a' `ltR` b'], [a' `gtR` b']]

termR :: Expr Rational -> Maybe Rat
termR (Const c) = return (constLC (numerator c), denominator c)
termR (Var v) = return (varLC v, 1)
termR (a :+: b) = do
  (t1,c1) <- termR a
  (t2,c2) <- termR b
  return (c2 .*. t1 .+. c1 .*. t2, c1*c2)
termR (a :*: b) = do
  (t1,c1) <- termR a
  (t2,c2) <- termR b
  msum [ do{ c <- asConst t1; return (c .*. t2, c1*c2) }
       , do{ c <- asConst t2; return (c .*. t1, c1*c2) }
       ]
termR (a :/: b) = do
  (t1,c1) <- termR a
  (t2,c2) <- termR b
  c3 <- asConst t2
  guard $ c3 /= 0
  return (c2 .*. t1, c1*c3)

leR, ltR, geR, gtR :: Rat -> Rat -> Lit
leR (lc1,c) (lc2,d) = Nonneg $ normalizeLCR $ c .*. lc2 .-. d .*. lc1
ltR (lc1,c) (lc2,d) = Pos $ normalizeLCR $ c .*. lc2 .-. d .*. lc1
geR = flip leR
gtR = flip gtR

normalizeLCR :: LCZ -> LCZ
normalizeLCR lc = mapLC (`div` d) lc
  where d = gcd' $ map snd $ IM.toList $ unLC lc

-- ---------------------------------------------------------------------------

{-
(ls1,ls2,us1,us2) represents
{ x | ∀(M,c)∈ls1. M/c≤x, ∀(M,c)∈ls2. M/c<x, ∀(M,c)∈us1. x≤M/c, ∀(M,c)∈us2. x<M/c }
-}
type BoundsR = ([Rat], [Rat], [Rat], [Rat])

eliminate :: Var -> [Lit] -> DNF Lit
eliminate v xs = DNF [rest] .&&. boundConditions bnd
  where
    (bnd, rest) = collectBounds v xs

collectBounds :: Var -> [Lit] -> (BoundsR, [Lit])
collectBounds v = foldr phi (([],[],[],[]),[])
  where
    phi :: Lit -> (BoundsR, [Lit]) -> (BoundsR, [Lit])
    phi lit@(Nonneg t) x = f False lit t x
    phi lit@(Pos t) x = f True lit t x

    f :: Bool -> Lit -> LCZ -> (BoundsR, [Lit]) -> (BoundsR, [Lit])
    f strict lit (LC t) (bnd@(ls1,ls2,us1,us2), xs) = 
      case c `compare` 0 of
        EQ -> (bnd, lit : xs)
        GT ->
          if strict
          then ((ls1, (lnegate t', c) : ls2, us1, us2), xs) -- 0 < cx + M ⇔ -M/c <  x
          else (((lnegate t', c) : ls1, ls2, us1, us2), xs) -- 0 ≤ cx + M ⇔ -M/c ≤ x
        LT -> 
          if strict
          then ((ls1, ls2, us1, (t', negate c) : us2), xs) -- 0 < cx + M ⇔ x < M/-c
          else ((ls1, ls2, (t', negate c) : us1, us2), xs) -- 0 ≤ cx + M ⇔ x ≤ M/-c
      where
        c = fromMaybe 0 $ IM.lookup v t
        t' = LC $ IM.delete v t

boundConditions :: BoundsR -> DNF Lit
boundConditions  (ls1, ls2, us1, us2) = DNF $ maybeToList $ simplify $ 
  [ x `leR` y | x <- ls1, y <- us1 ] ++
  [ x `ltR` y | x <- ls1, y <- us2 ] ++ 
  [ x `ltR` y | x <- ls2, y <- us1 ] ++
  [ x `ltR` y | x <- ls2, y <- us2 ]

eliminateQuantifiers :: Formula Rational -> Maybe (DNF Lit)
eliminateQuantifiers = f
  where
    f T = return true
    f F = return false
    f (Atom (Rel a op b)) = atomR op a b
    f (And a b) = liftM2 (.&&.) (f a) (f b)
    f (Or a b) = liftM2 (.||.) (f a) (f b)
    f (Not a) = f (pushNot a)
    f (Imply a b) = f (Or (Not a) b)
    f (Equiv a b) = f (And (Imply a b) (Imply b a))
    f (Forall v a) = do
      dnf <- f (Exists v (pushNot a))
      return (notF dnf)
    f (Exists v a) = do
      dnf <- f a
      return $ orF [eliminate v xs | xs <- unDNF dnf]

solve :: Formula Rational -> SatResult Rational
solve formula =
  case eliminateQuantifiers formula of
    Nothing -> Unknown
    Just dnf ->
      case msum [solve' vs xs | xs <- unDNF dnf] of
        Nothing -> Unsat
        Just m -> Sat m
  where
    vs = IS.toList (vars formula)

solve' :: [Var] -> [Lit] -> Maybe (Model Rational)
solve' vs xs = simplify xs >>= go vs
  where
    go [] [] = return IM.empty
    go [] _ = mzero
    go (v:vs) ys = msum (map f (unDNF (boundConditions bnd)))
      where
        (bnd, rest) = collectBounds v ys
        f zs = do
          model <- go vs (zs ++ rest)
          val <- pickup (evalBounds model bnd)
          return $ IM.insert v val model

evalBounds :: Model Rational -> BoundsR -> Interval Rational
evalBounds model (ls1,ls2,us1,us2) =
  foldl' Interval.intersection univ $ 
    [ interval (Just (True, evalRat model x)) Nothing  | x <- ls1 ] ++
    [ interval (Just (False, evalRat model x)) Nothing | x <- ls2 ] ++
    [ interval Nothing (Just (True, evalRat model x))  | x <- us1 ] ++
    [ interval Nothing (Just (False, evalRat model x)) | x <- us2 ]

-- ---------------------------------------------------------------------------

constraintsToDNF :: [Constraint Rational] -> DNF Lit
constraintsToDNF = andF . map constraintToDNF

constraintToDNF :: Constraint Rational -> DNF Lit
constraintToDNF (LARel a op b) = DNF $
  case op of
    Eql -> [[Nonneg c, Nonneg (lnegate c)]]
    NEq -> [[Pos c], [Pos (lnegate c)]]
    Ge  -> [[Nonneg c]]
    Le  -> [[Nonneg (lnegate c)]]
    Gt  -> [[Pos c]]
    Lt  -> [[Pos (lnegate c)]]
  where
    c = normalize (a .-. b)

    normalize :: LC Rational -> LCZ
    normalize (LC m)
      | IM.null m = LC IM.empty
      | otherwise = LC $ IM.map (round . (*c)) m
           where
             c = fromIntegral $ foldl' lcm 1 (map denominator (IM.elems m))

-- ---------------------------------------------------------------------------

gcd' :: [Integer] -> Integer
gcd' [] = 1
gcd' xs = foldl1' gcd xs

-- ---------------------------------------------------------------------------

{-
7x + 12y + 31z = 17
3x + 5y + 14z = 7
1 ≤ x ≤ 40
-50 ≤ y ≤ 50

satisfiable in R
but unsatisfiable in Z
-}
test1 :: Formula Rational
test1 = c1 .&&. c2 .&&. c3 .&&. c4
  where
    x = Var 0
    y = Var 1
    z = Var 2
    c1 = 7*x + 12*y + 31*z .==. 17
    c2 = 3*x + 5*y + 14*z .==. 7
    c3 = 1 .<=. x .&&. x .<=. 40
    c4 = (-50) .<=. y .&&. y .<=. 50

test1' :: [Constraint Rational]
test1' = [c1, c2] ++ c3 ++ c4
  where
    x = varLC 0
    y = varLC 1
    z = varLC 2
    c1 = 7.*.x .+. 12.*.y .+. 31.*.z .==. constLC 17
    c2 = 3.*.x .+. 5.*.y .+. 14.*.z .==. constLC 7
    c3 = [constLC 1 .<=. x, x .<=. constLC 40]
    c4 = [constLC (-50) .<=. y, y .<=. constLC 50]

{-
27 ≤ 11x+13y ≤ 45
-10 ≤ 7x-9y ≤ 4

satisfiable in R
but unsatisfiable in Z
-}
test2 :: Formula Rational
test2 = c1 .&&. c2
  where
    x = Var 0
    y = Var 1
    t1 = 11*x + 13*y
    t2 = 7*x - 9*y
    c1 = 27 .<=. t1 .&&. t1 .<=. 45
    c2 = (-10) .<=. t2 .&&. t2 .<=. 4

-- ---------------------------------------------------------------------------
