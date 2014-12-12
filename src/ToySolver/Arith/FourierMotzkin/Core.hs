{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Arith.FourierMotzkin.Core
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
module ToySolver.Arith.FourierMotzkin.Core
    (
    -- * Primitive constraints
      Constr (..)
    , ExprZ
    , fromLAAtom
    , toLAAtom
    , constraintsToDNF

    -- * Projection
    , project
    , project'
    , projectN
    , projectN'

    -- * Solving
    , solve
    , solve'

    -- * Utilities used by other modules
    , Rat
    , toRat
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

-- | Atomic constraint
data Constr
  = IsNonneg ExprZ
  | IsPos ExprZ
  | IsZero ExprZ
  deriving (Show, Eq, Ord)

instance Variables Constr where
  vars (IsPos t) = vars t
  vars (IsNonneg t) = vars t
  vars (IsZero t) = vars t

leR, ltR, geR, gtR, eqR :: Rat -> Rat -> Constr
leR (e1,c) (e2,d) = IsNonneg $ normalizeExpr $ c *^ e2 ^-^ d *^ e1
ltR (e1,c) (e2,d) = IsPos $ normalizeExpr $ c *^ e2 ^-^ d *^ e1
geR = flip leR
gtR = flip gtR
eqR (e1,c) (e2,d) = IsZero $ normalizeExpr $ c *^ e2 ^-^ d *^ e1

normalizeExpr :: ExprZ -> ExprZ
normalizeExpr e = LA.mapCoeff (`div` d) e
  where d = abs $ gcd' $ map fst $ LA.terms e

-- "subst1Constr x t c" computes c[t/x]
subst1Constr :: Var -> LA.Expr Rational -> Constr -> Constr
subst1Constr x t c =
  case c of
    IsPos e    -> IsPos (f e)
    IsNonneg e -> IsNonneg (f e)
    IsZero e   -> IsZero (f e)
  where
    f :: ExprZ -> ExprZ
    f = normalizeExpr . fst . toRat . LA.applySubst1 x t . LA.mapCoeff fromInteger

-- 制約集合の単純化
-- It returns Nothing when a inconsistency is detected.
simplify :: [Constr] -> Maybe [Constr]
simplify = fmap concat . mapM f
  where
    f :: Constr -> Maybe [Constr]
    f c@(IsPos e) =
      case LA.asConst e of
        Just x -> guard (x > 0) >> return []
        Nothing -> return [c]
    f c@(IsNonneg e) =
      case LA.asConst e of
        Just x -> guard (x >= 0) >> return []
        Nothing -> return [c]
    f c@(IsZero e) =
      case LA.asConst e of
        Just x -> guard (x == 0) >> return []
        Nothing -> return [c]

evalConstr :: Model Rational -> Constr -> Bool
evalConstr m (IsPos t)    = LA.evalExpr m (LA.mapCoeff fromInteger t) > 0
evalConstr m (IsNonneg t) = LA.evalExpr m (LA.mapCoeff fromInteger t) >= 0
evalConstr m (IsZero t)   = LA.evalExpr m (LA.mapCoeff fromInteger t) == 0

-- ---------------------------------------------------------------------------

fromLAAtom :: LA.Atom Rational -> DNF Constr
fromLAAtom (ArithRel a op b) = atomR' op (toRat a) (toRat b)
  where
    atomR' :: RelOp -> Rat -> Rat -> DNF Constr
    atomR' op a b = 
      case op of
        Le -> DNF [[a `leR` b]]
        Lt -> DNF [[a `ltR` b]]
        Ge -> DNF [[a `geR` b]]
        Gt -> DNF [[a `gtR` b]]
        Eql -> DNF [[a `eqR` b]]
        NEq -> DNF [[a `ltR` b], [a `gtR` b]]

toLAAtom :: Constr -> LA.Atom Rational
toLAAtom (IsNonneg e) = LA.mapCoeff fromInteger e .>=. LA.constant 0
toLAAtom (IsPos e)    = LA.mapCoeff fromInteger e .>.  LA.constant 0
toLAAtom (IsZero e)   = LA.mapCoeff fromInteger e .==. LA.constant 0

constraintsToDNF :: [LA.Atom Rational] -> DNF Constr
constraintsToDNF = andB . map fromLAAtom

-- ---------------------------------------------------------------------------

{-
(ls1,ls2,us1,us2) represents
{ x | ∀(M,c)∈ls1. M/c≤x, ∀(M,c)∈ls2. M/c<x, ∀(M,c)∈us1. x≤M/c, ∀(M,c)∈us2. x<M/c }
-}
type BoundsR = ([Rat], [Rat], [Rat], [Rat])

evalBounds :: Model Rational -> BoundsR -> Interval Rational
evalBounds model (ls1,ls2,us1,us2) =
  Interval.intersections $
    [ Finite (evalRat model x) <=..< PosInf | x <- ls1 ] ++
    [ Finite (evalRat model x) <..<  PosInf | x <- ls2 ] ++
    [ NegInf <..<= Finite (evalRat model x) | x <- us1 ] ++
    [ NegInf <..<  Finite (evalRat model x) | x <- us2 ]

boundsToConstrs :: BoundsR -> Maybe [Constr]
boundsToConstrs  (ls1, ls2, us1, us2) = simplify $ 
  [ x `leR` y | x <- ls1, y <- us1 ] ++
  [ x `ltR` y | x <- ls1, y <- us2 ] ++ 
  [ x `ltR` y | x <- ls2, y <- us1 ] ++
  [ x `ltR` y | x <- ls2, y <- us2 ]

collectBounds :: Var -> [Constr] -> (BoundsR, [Constr])
collectBounds v = foldr phi (([],[],[],[]),[])
  where
    phi :: Constr -> (BoundsR, [Constr]) -> (BoundsR, [Constr])
    phi constr@(IsNonneg t) x = f False constr t x
    phi constr@(IsPos t) x = f True constr t x
    phi constr@(IsZero _) (bnd, xs) = (bnd, constr : xs) -- XXX: we assume v does not appear in constr

    f :: Bool -> Constr -> ExprZ -> (BoundsR, [Constr]) -> (BoundsR, [Constr])
    f strict constr t (bnd@(ls1,ls2,us1,us2), xs) =
      case LA.extract v t of
        (c,t') ->
          case c `compare` 0 of
            EQ -> (bnd, constr : xs)
            GT ->
              if strict
              then ((ls1, (negateV t', c) : ls2, us1, us2), xs) -- 0 < cx + M ⇔ -M/c <  x
              else (((negateV t', c) : ls1, ls2, us1, us2), xs) -- 0 ≤ cx + M ⇔ -M/c ≤ x
            LT ->
              if strict
              then ((ls1, ls2, us1, (t', negate c) : us2), xs) -- 0 < cx + M ⇔ x < M/-c
              else ((ls1, ls2, (t', negate c) : us1, us2), xs) -- 0 ≤ cx + M ⇔ x ≤ M/-c

-- ---------------------------------------------------------------------------

project :: Var -> [LA.Atom Rational] -> [([LA.Atom Rational], Model Rational -> Model Rational)]
project v xs = do
  ys <- unDNF $ constraintsToDNF xs
  (zs, mt) <- maybeToList $ project' v ys
  return (map toLAAtom zs, mt)

project' :: Var -> [Constr] -> Maybe ([Constr], Model Rational -> Model Rational)
project' v cs | Just (vdef,cs') <- findEq v cs = do
  let mt m = IM.insert v (evalRat m vdef) m
  return ([subst1Constr v (fromRat vdef) c | c <- cs'], mt)
project' v xs = do
  case collectBounds v xs of
    (bnd, rest) -> do
      cond <- boundsToConstrs bnd
      let mt m =
           case Interval.simplestRationalWithin (evalBounds m bnd) of
             Nothing  -> error "ToySolver.FourierMotzkin.project': should not happen"
             Just val -> IM.insert v val m
      return (rest ++ cond, mt)

projectN :: VarSet -> [LA.Atom Rational] -> [([LA.Atom Rational], Model Rational -> Model Rational)]
projectN vs xs = do
  ys <- unDNF $ constraintsToDNF xs
  (zs, mt) <- maybeToList $ projectN' vs ys
  return (map toLAAtom zs, mt)

projectN' :: VarSet -> [Constr] -> Maybe ([Constr], Model Rational -> Model Rational)
projectN' vs2 xs2 = do
  (zs, mt) <- f (IS.toList vs2) xs2
  return (zs, mt)
  where
    f [] xs     = return (xs, id)
    f (v:vs) xs = do
      (ys, mt1) <- project' v xs
      (zs, mt2) <- f vs ys
      return (zs, mt1 . mt2)

findEq :: Var -> [Constr] -> Maybe (Rat, [Constr])
findEq v = msum . map f . pickup
  where
    pickup :: [a] -> [(a,[a])]
    pickup [] = []
    pickup (x:xs) = (x,xs) : [(y,x:ys) | (y,ys) <- pickup xs]

    f :: (Constr, [Constr]) -> Maybe (Rat, [Constr])
    f (IsZero e, cs) = do
      (c, e') <- LA.extractMaybe v e
      return ((negateV e', c), cs)
    f _ = Nothing

solve :: VarSet -> [LA.Atom Rational] -> Maybe (Model Rational)
solve vs cs = msum [solve' vs cs2 | cs2 <- unDNF (constraintsToDNF cs)]

solve' :: VarSet -> [Constr] -> Maybe (Model Rational)
solve' vs cs = do
  (cs2,mt) <- projectN' vs =<< simplify cs
  let m = IM.empty
  guard $ all (evalConstr m) cs2
  return $ mt m

-- ---------------------------------------------------------------------------

gcd' :: [Integer] -> Integer
gcd' [] = 1
gcd' xs = foldl1' gcd xs

-- ---------------------------------------------------------------------------
