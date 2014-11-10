{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.FourierMotzkin.Core
-- Copyright   :  (c) Masahiro Sakai 2011-2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Naïve implementation of Fourier-Motzkin Variable Elimination
-- 
-- Reference:
--
-- * <http://users.cecs.anu.edu.au/~michaeln/pubs/arithmetic-dps.pdf>
--
-----------------------------------------------------------------------------
module ToySolver.FourierMotzkin.Core
    ( ExprZ
    , Rat
    , toRat
    , fromRat

    , Lit (..)
    , leR, ltR, geR, gtR
    , simplify

    , fromLAAtom
    , toLAAtom
    , constraintsToDNF

    , BoundsR
    , collectBounds
    , boundsToLits
    , evalBounds

    , project
    , project'
    , projectN
    , projectN'
    , solve
    , solve'
    ) where

import Control.Monad
import Data.List
import Data.Maybe
import Data.Ratio
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Data.VectorSpace hiding (project)
import qualified Data.Interval as Interval
import Data.Interval (Interval, Extended (..), (<=..<), (<..<=), (<..<))

import ToySolver.Data.ArithRel
import ToySolver.Data.Boolean
import ToySolver.Data.DNF
import qualified ToySolver.Data.LA as LA
import ToySolver.Data.Var

-- ---------------------------------------------------------------------------

type ExprZ = LA.Expr Integer

normalizeExprR :: ExprZ -> ExprZ
normalizeExprR e = LA.mapCoeff (`div` d) e
  where d = abs $ gcd' $ map fst $ LA.terms e

-- ---------------------------------------------------------------------------

-- | (t,c) represents t/c, and c must be >0.
type Rat = (ExprZ, Integer)

toRat :: LA.Expr Rational -> Rat
toRat e = seq m $ (LA.mapCoeff f e, m)
  where
    f x = numerator (fromInteger m * x)
    m = foldl' lcm 1 [denominator c | (c,_) <- LA.terms e]

fromRat :: Rat -> LA.Expr Rational
fromRat (e,c) = LA.mapCoeff (% c) e

evalRat :: Model Rational -> Rat -> Rational
evalRat model (e, d) = LA.lift1 1 (model IM.!) (LA.mapCoeff fromIntegral e) / (fromIntegral d)

-- ---------------------------------------------------------------------------

-- | Literal
data Lit = Nonneg ExprZ | Pos ExprZ deriving (Show, Eq, Ord)

instance Variables Lit where
  vars (Pos t) = vars t
  vars (Nonneg t) = vars t

instance Complement Lit where
  notB (Pos t) = Nonneg (negateV t)
  notB (Nonneg t) = Pos (negateV t)

leR, ltR, geR, gtR :: Rat -> Rat -> Lit
leR (e1,c) (e2,d) = Nonneg $ normalizeExprR $ c *^ e2 ^-^ d *^ e1
ltR (e1,c) (e2,d) = Pos $ normalizeExprR $ c *^ e2 ^-^ d *^ e1
geR = flip leR
gtR = flip gtR

-- 制約集合の単純化
-- It returns Nothing when a inconsistency is detected.
simplify :: [Lit] -> Maybe [Lit]
simplify = fmap concat . mapM f
  where
    f :: Lit -> Maybe [Lit]
    f lit@(Pos e) =
      case LA.asConst e of
        Just x -> guard (x > 0) >> return []
        Nothing -> return [lit]
    f lit@(Nonneg e) =
      case LA.asConst e of
        Just x -> guard (x >= 0) >> return []
        Nothing -> return [lit]

-- ---------------------------------------------------------------------------

fromLAAtom :: LA.Atom Rational -> DNF Lit
fromLAAtom (ArithRel a op b) = atomR' op (toRat a) (toRat b)

toLAAtom :: Lit -> LA.Atom Rational
toLAAtom (Nonneg e) = LA.mapCoeff fromInteger e .>=. LA.constant 0
toLAAtom (Pos e)    = LA.mapCoeff fromInteger e .>. LA.constant 0

constraintsToDNF :: [LA.Atom Rational] -> DNF Lit
constraintsToDNF = andB . map fromLAAtom

atomR' :: RelOp -> Rat -> Rat -> DNF Lit
atomR' op a b = 
  case op of
    Le -> DNF [[a `leR` b]]
    Lt -> DNF [[a `ltR` b]]
    Ge -> DNF [[a `geR` b]]
    Gt -> DNF [[a `gtR` b]]
    Eql -> DNF [[a `leR` b, a `geR` b]]
    NEq -> DNF [[a `ltR` b], [a `gtR` b]]

-- ---------------------------------------------------------------------------

{-
(ls1,ls2,us1,us2) represents
{ x | ∀(M,c)∈ls1. M/c≤x, ∀(M,c)∈ls2. M/c<x, ∀(M,c)∈us1. x≤M/c, ∀(M,c)∈us2. x<M/c }
-}
type BoundsR = ([Rat], [Rat], [Rat], [Rat])

project :: Var -> [LA.Atom Rational] -> [([LA.Atom Rational], Model Rational -> Model Rational)]
project v xs = do
  ys <- unDNF $ constraintsToDNF xs
  (zs, mt) <- maybeToList $ project' v ys
  return (map toLAAtom zs, mt)

project' :: Var -> [Lit] -> Maybe ([Lit], Model Rational -> Model Rational)
project' v xs = do
  case collectBounds v xs of
    (bnd, rest) -> do
      cond <- boundsToLits bnd
      let mt m =
           case Interval.pickup (evalBounds m bnd) of
             Nothing  -> error "ToySolver.FourierMotzkin.project': should not happen"
             Just val -> IM.insert v val m
      return (rest ++ cond, mt)

projectN :: VarSet -> [LA.Atom Rational] -> [([LA.Atom Rational], Model Rational -> Model Rational)]
projectN vs xs = do
  ys <- unDNF $ constraintsToDNF xs
  (zs, mt) <- maybeToList $ projectN' vs ys
  return (map toLAAtom zs, mt)

projectN' :: VarSet -> [Lit] -> Maybe ([Lit], Model Rational -> Model Rational)
projectN' vs2 xs2 = do
  (zs, mt) <- f (IS.toList vs2) xs2
  return (zs, mt)
  where
    f [] xs     = return (xs, id)
    f (v:vs) xs = do
      (ys, mt1) <- project' v xs
      (zs, mt2) <- f vs ys
      return (zs, mt1 . mt2)

collectBounds :: Var -> [Lit] -> (BoundsR, [Lit])
collectBounds v = foldr phi (([],[],[],[]),[])
  where
    phi :: Lit -> (BoundsR, [Lit]) -> (BoundsR, [Lit])
    phi lit@(Nonneg t) x = f False lit t x
    phi lit@(Pos t) x = f True lit t x

    f :: Bool -> Lit -> ExprZ -> (BoundsR, [Lit]) -> (BoundsR, [Lit])
    f strict lit t (bnd@(ls1,ls2,us1,us2), xs) =
      case LA.extract v t of
        (c,t') ->
          case c `compare` 0 of
            EQ -> (bnd, lit : xs)
            GT ->
              if strict
              then ((ls1, (negateV t', c) : ls2, us1, us2), xs) -- 0 < cx + M ⇔ -M/c <  x
              else (((negateV t', c) : ls1, ls2, us1, us2), xs) -- 0 ≤ cx + M ⇔ -M/c ≤ x
            LT ->
              if strict
              then ((ls1, ls2, us1, (t', negate c) : us2), xs) -- 0 < cx + M ⇔ x < M/-c
              else ((ls1, ls2, (t', negate c) : us1, us2), xs) -- 0 ≤ cx + M ⇔ x ≤ M/-c

boundsToLits :: BoundsR -> Maybe [Lit]
boundsToLits  (ls1, ls2, us1, us2) = simplify $ 
  [ x `leR` y | x <- ls1, y <- us1 ] ++
  [ x `ltR` y | x <- ls1, y <- us2 ] ++ 
  [ x `ltR` y | x <- ls2, y <- us1 ] ++
  [ x `ltR` y | x <- ls2, y <- us2 ]

solve :: VarSet -> [LA.Atom Rational] -> Maybe (Model Rational)
solve vs cs = msum [solve' vs cs2 | cs2 <- unDNF (constraintsToDNF cs)]

solve' :: VarSet -> [Lit] -> Maybe (Model Rational)
solve' vs cs = do
  (ys,mt) <- projectN' vs =<< simplify cs
  guard $ Just [] == simplify ys
  return $ mt IM.empty

evalBounds :: Model Rational -> BoundsR -> Interval Rational
evalBounds model (ls1,ls2,us1,us2) =
  Interval.intersections $
    [ Finite (evalRat model x) <=..< PosInf | x <- ls1 ] ++
    [ Finite (evalRat model x) <..<  PosInf | x <- ls2 ] ++
    [ NegInf <..<= Finite (evalRat model x) | x <- us1 ] ++
    [ NegInf <..<  Finite (evalRat model x) | x <- us2 ]

-- ---------------------------------------------------------------------------

gcd' :: [Integer] -> Integer
gcd' [] = 1
gcd' xs = foldl1' gcd xs

-- ---------------------------------------------------------------------------
