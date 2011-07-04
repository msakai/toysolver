{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Cooper
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Naive implementation of Cooper's algorithm
--
-- http://hagi.is.s.u-tokyo.ac.jp/pub/staff/hagiya/kougiroku/ronri/5.txt
-- http://www.cs.cmu.edu/~emc/spring06/home1_files/Presburger%20Arithmetic.ppt
-- 
-----------------------------------------------------------------------------
module Cooper
    ( module Expr
    , module Formula
    , Lit (..)
    , Formula' (..)
    , eliminateQuantifiers
    , solve
    , solveQFLA
    , Model
    ) where

import Control.Monad
import Data.Maybe
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS

import Expr
import Formula
import LA
import qualified FourierMotzkin as FM
import qualified Interval

-- ---------------------------------------------------------------------------

type LCZ = LC Integer

atomZ :: RelOp -> Expr Rational -> Expr Rational -> Maybe Formula'
atomZ op a b = do
  (lc1,c1) <- FM.termR a
  (lc2,c2) <- FM.termR b
  let a' = c2 .*. lc1
      b' = c1 .*. lc2
  case op of
    Le -> return $ Lit $ a' `leZ` b'
    Lt -> return $ Lit $ a' `ltZ` b'
    Ge -> return $ Lit $ a' `geZ` b'
    Gt -> return $ Lit $ a' `gtZ` b'
    Eql -> return $ eqZ a' b'
    NEq -> liftM notF (atomZ Eql a b)

leZ, ltZ, geZ, gtZ :: LCZ -> LCZ -> Lit
leZ lc1 lc2 = lc1 `ltZ` (lc2 .+. constLC 1)
ltZ lc1 lc2 = Pos $ (lc2 .-. lc1)
geZ = flip leZ
gtZ = flip gtZ

eqZ :: LCZ -> LCZ -> Formula'
eqZ lc1 lc2 = Lit (lc1 `leZ` lc2) .&&. Lit (lc1 `geZ` lc2)

-- | Literal
data Lit
    = Pos LCZ
    | Divisible Bool Integer LCZ
    deriving (Show, Eq, Ord)

instance Variables Lit where
  vars (Pos t) = vars t
  vars (Divisible _ _ t) = vars t

instance Complement Lit where
  notF (Pos lc) = lc `leZ` constLC 0
  notF (Divisible b c lc) = Divisible (not b) c lc

data Formula'
    = T'
    | F'
    | And' Formula' Formula'
    | Or' Formula' Formula'
    | Lit Lit
    deriving (Show, Eq, Ord)

instance Complement Formula' where
  notF T' = F'
  notF F' = T'
  notF (And' a b) = Or' (notF a) (notF b)
  notF (Or' a b) = And' (notF a) (notF b)
  notF (Lit lit) = Lit (notF lit)

instance Boolean Formula' where
  true = T'
  false = F'
  (.&&.) = And'
  (.||.) = Or'

subst1 :: Var -> LCZ -> Formula' -> Formula'
subst1 x lc = go
  where
    go T' = T'
    go F' = F'
    go (And' a b) = And' (go a) (go b)
    go (Or' a b) = Or' (go a) (go b)
    go (Lit (Divisible b c lc1)) = Lit $ Divisible b c $ subst1' x lc lc1
    go (Lit (Pos lc1)) = Lit $ Pos $ subst1' x lc lc1

subst1' :: Var -> LCZ -> LCZ -> LCZ
subst1' x lc lc1@(LC m) =
  case IM.lookup x m of
    Nothing -> lc1
    Just c -> c .*. lc .+. LC (IM.delete x m)

simplify :: Formula' -> Formula'
simplify T' = T'
simplify F' = F'
simplify (And' a b) =
  case (simplify a, simplify b) of
    (T', b') -> b'
    (a', T') -> a'
    (F', _) -> false
    (_, F') -> false
    (a',b') -> a' .&&. b'
simplify (Or' a b) =
  case (simplify a, simplify b) of
    (F', b') -> b'
    (a', F') -> a'
    (T', _) -> true
    (_, T') -> true
    (a',b') -> a' .||. b'
simplify lit@(Lit (Pos lc)) =
  case asConst lc of
    Nothing -> lit
    Just c -> if c > 0 then true else false
simplify lit@(Lit (Divisible b c lc@(LC m))) = 
  case asConst lc of
    Just c' ->
      if b == (c' `mod` c == 0) then true else false
    Nothing
      | c==d -> if b then true else false
      | d==1 -> lit
      | otherwise -> Lit (Divisible b (c `div` d) (LC (IM.map (`div` d) m)))
  where
    d = foldl gcd c (IM.elems m)

-- ---------------------------------------------------------------------------

data Witness = WCase1 Integer LCZ | WCase2 Integer Integer Integer [LCZ]

eliminateZ :: Var -> Formula' -> Formula'
eliminateZ x formula = simplify $ orF $ map fst $ eliminateZ' x formula

eliminateZ' :: Var -> Formula' -> [(Formula', Witness)]
eliminateZ' x formula = case1 ++ case2
  where
    c :: Integer
    c = f formula
      where
         f :: Formula' -> Integer
         f T' = 1
         f F' = 1
         f (And' a b) = lcm (f a) (f b)
         f (Or' a b) = lcm (f a) (f b)
         f (Lit (Pos (LC m))) = fromMaybe 1 (IM.lookup x m)
         f (Lit (Divisible _ _ (LC m))) = fromMaybe 1 (IM.lookup x m)
    
    formula1 :: Formula'
    formula1 = f formula .&&. Lit (Divisible True c (varLC x))
      where
        f :: Formula' -> Formula'
        f T' = T'
        f F' = F'
        f (And' a b) = f a .&&. f b
        f (Or' a b) = f a .||. f b
        f lit@(Lit (Pos (LC m))) =
          case IM.lookup x m of
            Nothing -> lit
            Just a ->
              let e = c `div` abs a
              in Lit $ Pos $ LC $ IM.mapWithKey (\x' c' -> if x==x' then signum c' else e*c') m
        f lit@(Lit (Divisible b d (LC m))) =
          case IM.lookup x m of
            Nothing -> lit
            Just a ->
              let e = c `div` abs a
              in Lit $ Divisible b (e*d) $ LC $ IM.mapWithKey (\x' c' -> if x==x' then signum c' else e*c') m

    delta :: Integer
    delta = f formula1
      where
        f :: Formula' -> Integer
        f T' = 1
        f F' = 1
        f (And' a b) = lcm (f a) (f b)
        f (Or' a b) = lcm (f a) (f b)
        f (Lit (Divisible _ c' _)) = c'
        f (Lit (Pos _)) = 1

    bs :: [LCZ]
    bs = f formula1
      where
        f :: Formula' -> [LCZ]
        f T' = []
        f F' = []
        f (And' a b) = f a ++ f b
        f (Or' a b) = f a ++ f b
        f (Lit (Divisible _ _ _)) = []
        f (Lit (Pos (LC m))) =
            case IM.lookup x m of
              Nothing -> []
              Just c' -> if c' > 0 then [lnegate (LC (IM.delete x m))] else [LC (IM.delete x m)]    

    case1 :: [(Formula', Witness)]
    case1 = [ (subst1 x lc formula1, WCase1 c lc)
            | j <- [1..delta], b <- bs, let lc = b .+. constLC j ]

    p :: Formula'
    p = f formula1
      where        
        f :: Formula' -> Formula'
        f T' = T'
        f F' = F'
        f (And' a b) = f a .&&. f b
        f (Or' a b) = f a .||. f b
        f lit@(Lit (Pos (LC m))) =
          case IM.lookup x m of
            Nothing -> lit
            Just c -> if c < 0 then T' else F'
        f lit@(Lit (Divisible _ _ _)) = lit

    us :: [LCZ]
    us = f formula1
      where
        f :: Formula' -> [LCZ]
        f T' = []
        f F' = []
        f (And' a b) = f a ++ f b
        f (Or' a b) = f a ++ f b
        f (Lit (Pos (LC m))) =
          case IM.lookup x m of
            Nothing -> []
            Just c -> if c < 0 then [LC (IM.delete x m)] else []
        f (Lit (Divisible _ _ _)) = []

    case2 :: [(Formula', Witness)]
    case2 = [(subst1 x (constLC j) p, WCase2 c j delta us) | j <- [1..delta]]

evalWitness :: Model Integer -> Witness -> Integer
evalWitness model (WCase1 c lc) = evalLC model lc `div` c
evalWitness model (WCase2 c j delta us)
  | null us' = j `div` c
  | otherwise = (j + (((u - delta - 1) `div` delta) * delta)) `div` c
  where
    us' = map (evalLC model) us
    u = minimum us'

-- ---------------------------------------------------------------------------

eliminateQuantifiers :: Formula Rational -> Maybe Formula'
eliminateQuantifiers = f
  where
    f T = return T'
    f F = return F'
    f (Atom (Rel lc1 op lc2)) = atomZ op lc1 lc2
    f (And a b) = liftM2 (.&&.) (f a) (f b)
    f (Or a b) = liftM2 (.||.) (f a) (f b)
    f (Not a) = f (pushNot a)
    f (Imply a b) = f $ Or (Not a) b
    f (Equiv a b) = f $ And (Imply a b) (Imply b a)
    f (Forall x body) = liftM notF $ f $ Exists x $ pushNot body
    f (Exists x body) = liftM (eliminateZ x) (f body)

-- ---------------------------------------------------------------------------

solve :: Formula Rational -> SatResult Integer
solve formula =
  case eliminateQuantifiers formula of
    Nothing -> Unknown
    Just formula' ->
       case solve' vs formula' of
         Nothing -> Unsat
         Just m -> Sat m
  where
    vs = IS.toList (vars formula)

solve' :: [Var] -> Formula' -> Maybe (Model Integer)
solve' vs formula = go vs (simplify formula)
  where
    go [] T' = return IM.empty
    go [] _ = mzero
    go (v:vs) formula = do
      let xs = eliminateZ' v formula
      msum $ flip map xs $ \(formula', witness) -> do
        model <- go vs (simplify formula')
        let val = evalWitness model witness 
        return $ IM.insert v val model

-- ---------------------------------------------------------------------------

solveQFLA :: [Constraint Rational] -> VarSet -> Maybe (Model Rational)
solveQFLA cs ivs = msum [ FM.simplify xs >>= go (IS.toList rvs) | xs <- unDNF dnf ]
  where
    vs  = vars cs
    rvs = vs `IS.difference` ivs
    dnf = FM.constraintsToDNF cs

    go :: [Var] -> [FM.Lit] -> Maybe (Model Rational)
    go [] xs = fmap (fmap fromIntegral) $ solve' (IS.toList ivs) (foldr And' T' (map f xs))
    go (v:vs) ys = msum (map f (unDNF (FM.boundConditions bnd)))
      where
        (bnd, rest) = FM.collectBounds v ys
        f zs = do
          model <- go vs (zs ++ rest)
          val <- Interval.pickup (FM.evalBounds model bnd)
          return $ IM.insert v val model

    f :: FM.Lit -> Formula'
    f (FM.Nonneg lc) = Lit $ lc `geZ` (constLC 0)
    f (FM.Pos lc)    = Lit $ lc `gtZ` (constLC 0)

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
