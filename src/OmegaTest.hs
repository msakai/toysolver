{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  OmegaTest
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- (incomplete) implementation of Omega Test
-- 
-- see http://users.cecs.anu.edu.au/~michaeln/pubs/arithmetic-dps.pdf for detail
--
-- References:
--
-- William Pugh. The Omega test: a fast and practical integer
-- programming algorithm for dependence analysis. In Proceedings of
-- the 1991 ACM/IEEE conference on Supercomputing (1991), pp. 4-13.
-----------------------------------------------------------------------------
module OmegaTest
    ( module Expr
    , module Formula
    , module LA
    , Lit (..)
    , eliminateQuantifiers
    , solve
    , solveQFLA
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
import qualified Interval
import Util (combineMaybe)
import qualified FourierMotzkin as FM
import FourierMotzkin (Lit (..), Rat (..))

-- ---------------------------------------------------------------------------

type LCZ = LC Integer

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

atomZ :: RelOp -> Expr Rational -> Expr Rational -> Maybe (DNF Lit)
atomZ op a b = do
  (lc1,c1) <- FM.termR a
  (lc2,c2) <- FM.termR b
  let a' = c2 .*. lc1
      b' = c1 .*. lc2
  return $ case op of
    Le -> DNF [[a' `leZ` b']]
    Lt -> DNF [[a' `ltZ` b']]
    Ge -> DNF [[a' `geZ` b']]
    Gt -> DNF [[a' `gtZ` b']]
    Eql -> eqZ a' b'
    NEq -> DNF [[a' `ltZ` b'], [a' `gtZ` b']]

leZ, ltZ, geZ, gtZ :: LCZ -> LCZ -> Lit
-- Note that constants may be floored by division
leZ lc1 lc2 = Nonneg (LC (IM.map (`div` d) m))
  where
    LC m = lc2 .-. lc1
    d = gcd' [c | (v,c) <- IM.toList m, v /= constKey]
ltZ lc1 lc2 = (lc1 .+. constLC 1) `leZ` lc2
geZ = flip leZ
gtZ = flip gtZ

eqZ :: LCZ -> LCZ -> (DNF Lit)
eqZ lc1 lc2
  = if fromMaybe 0 (IM.lookup constKey m) `mod` d == 0
    then DNF [[Nonneg lc, Nonneg (lnegate lc)]]
    else false
  where
    LC m = lc1 .-. lc2
    lc = LC (IM.map (`div` d) m)
    d = gcd' [c | (v,c) <- IM.toList m, v /= constKey]

-- ---------------------------------------------------------------------------

{-
(ls,us) represents
{ x | ∀(M,c)∈ls. M/c≤x, ∀(M,c)∈us. x≤M/c }
-}
type BoundsZ = ([Rat],[Rat])

eliminate :: Var -> [Lit] -> DNF Lit
eliminate v xs = DNF [rest] .&&. boundConditionsZ bnd
   where
     (bnd,rest) = collectBoundsZ v xs

collectBoundsZ :: Var -> [Lit] -> (BoundsZ,[Lit])
collectBoundsZ v = foldr phi (([],[]),[])
  where
    phi :: Lit -> (BoundsZ,[Lit]) -> (BoundsZ,[Lit])
    phi (Pos t) x = phi (Nonneg (t .-. constLC 1)) x
    phi lit@(Nonneg (LC t)) ((ls,us),xs) =
      case c `compare` 0 of
        EQ -> ((ls, us), lit : xs)
        GT -> (((lnegate t', c) : ls, us), xs) -- 0 ≤ cx + M ⇔ -M/c ≤ x
        LT -> ((ls, (t', negate c) : us), xs)   -- 0 ≤ cx + M ⇔ x ≤ M/-c
      where
        c = fromMaybe 0 $ IM.lookup v t
        t' = LC $ IM.delete v t

boundConditionsZ :: BoundsZ -> DNF Lit
boundConditionsZ (ls,us) = DNF $ catMaybes $ map simplify $
  if isExact (ls,us)
    then [cond1]
    else cond1 : cond2
  where
     cond1 =
       [ constLC ((a-1)*(b-1)) `leZ` (a .*. d .-. b .*. c)
       | (c,a)<-ls , (d,b)<-us ]
     cond2 = 
       [ [(a' .*. c) `leZ` (a .*. val) | (c,a)<-ls] ++
         [(b .*. val) `geZ` (a' .*. d) | (d,b)<-us]
       | not (null us)
       , let m = maximum [b | (_,b)<-us]
       ,  (c',a') <- ls
       , k <- [0 .. (m*a'-a'-m) `div` m]
       , let val = c' .+. constLC k
       -- x = val / a'
       -- c / a ≤ x ⇔ c / a ≤ val / a' ⇔ a' c ≤ a val
       -- x ≤ d / b ⇔ val / a' ≤ d / b ⇔ b val ≤ a' d
       ]

isExact :: BoundsZ -> Bool
isExact (ls,us) = and [a==1 || b==1 | (c,a)<-ls , (d,b)<-us]

eliminateQuantifiers :: Formula Rational -> Maybe (DNF Lit)
eliminateQuantifiers = f
  where
    f T = return true
    f F = return false
    f (Atom (Rel a op b)) = atomZ op a b
    f (And a b) = liftM2 (.&&.) (f a) (f b)
    f (Or a b) = liftM2 (.||.) (f a) (f b)
    f (Not a) = f (pushNot a)
    f (Imply a b) = f (Or (Not a) b)
    f (Equiv a b) = f (And (Imply a b) (Imply b a))
    f (Forall v a) = do
      dnf <- f (Exists v (pushNot a))
      return $ notF dnf
    f (Exists v a) = do
      dnf <- f a
      return $ orF [eliminate v xs | xs <- unDNF dnf]

solve :: Formula Rational -> SatResult Integer
solve formula =
  case eliminateQuantifiers formula of
    Nothing -> Unknown
    Just dnf ->
      case msum [solve' vs xs | xs <- unDNF dnf] of
        Nothing -> Unsat
        Just m -> Sat m
  where
    vs = IS.toList (vars formula)

solve' :: [Var] -> [Lit] -> Maybe (Model Integer)
solve' vs xs = simplify xs >>= go vs
  where
    go :: [Var] -> [Lit] -> Maybe (Model Integer)
    go [] [] = return IM.empty
    go [] _ = mzero
    go vs ys = msum (map f (unDNF (boundConditionsZ bnd)))
      where
        (v,vs',bnd,rest) = chooseVariable vs ys
        f zs = do
          model <- go vs' (zs ++ rest)
          val <- pickupZ (evalBoundsZ model bnd)
          return $ IM.insert v val model

chooseVariable :: [Var] -> [Lit] -> (Var, [Var], BoundsZ, [Lit])
chooseVariable vs xs = head $ [e | e@(_,_,bnd,_) <- table, isExact bnd] ++ table
  where
    table = [ (v, vs', bnd, rest)
            | (v,vs') <- pickup vs, let (bnd, rest) = collectBoundsZ v xs
            ]

evalBoundsZ :: Model Integer -> BoundsZ -> IntervalZ
evalBoundsZ model (ls,us) =
  foldl' intersectZ univZ $ 
    [ (Just (ceiling (evalLC model x % c)), Nothing) | (x,c) <- ls ] ++ 
    [ (Nothing, Just (floor (evalLC model x % c))) | (x,c) <- us ]

-- ---------------------------------------------------------------------------

type IntervalZ = (Maybe Integer, Maybe Integer)

univZ :: IntervalZ
univZ = (Nothing, Nothing)

intersectZ :: IntervalZ -> IntervalZ -> IntervalZ
intersectZ (l1,u1) (l2,u2) = (combineMaybe max l1 l2, combineMaybe min u1 u2)

pickupZ :: IntervalZ -> Maybe Integer
pickupZ (Nothing,Nothing) = return 0
pickupZ (Just x, Nothing) = return x
pickupZ (Nothing, Just x) = return x
pickupZ (Just x, Just y) = if x <= y then return x else mzero 

-- ---------------------------------------------------------------------------

solveQFLA :: [Constraint Rational] -> VarSet -> Maybe (Model Rational)
solveQFLA cs ivs = msum [ simplify xs >>= go (IS.toList rvs) | xs <- unDNF dnf ]
  where
    vs  = vars cs
    rvs = vs `IS.difference` ivs
    dnf = constraintsToDNF cs

    go :: [Var] -> [Lit] -> Maybe (Model Rational)
    go [] xs = fmap (fmap fromIntegral) $ solve' (IS.toList ivs) xs
    go (v:vs) ys = msum (map f (unDNF (FM.boundConditions bnd)))
      where
        (bnd, rest) = FM.collectBounds v ys
        f zs = do
          model <- go vs (zs ++ rest)
          val <- Interval.pickup (FM.evalBounds model bnd)
          return $ IM.insert v val model

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

pickup :: [a] -> [(a,[a])]
pickup [] = []
pickup (x:xs) = (x,xs) : [(y,x:ys) | (y,ys) <- pickup xs]

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
