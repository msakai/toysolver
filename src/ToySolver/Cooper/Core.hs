{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Cooper.Core
-- Copyright   :  (c) Masahiro Sakai 2011-2013
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (FlexibleInstances)
--
-- Naive implementation of Cooper's algorithm
--
-- Reference:
-- 
-- * <http://hagi.is.s.u-tokyo.ac.jp/pub/staff/hagiya/kougiroku/ronri/5.txt>
-- 
-- * <http://www.cs.cmu.edu/~emc/spring06/home1_files/Presburger%20Arithmetic.ppt>
-- 
-- See also:
--
-- * <http://hackage.haskell.org/package/presburger>
--
-----------------------------------------------------------------------------
module ToySolver.Cooper.Core
    (
    -- * Language of presburger arithmetics
      ExprZ
    , Lit (..)
    , evalLit
    , QFFormula (..)
    , fromLAAtom
    , (.|.)
    , evalQFFormula

    -- * Projection
    , project
    , projectN
    , projectCases
    , projectCasesN

    -- * Constraint solving
    , solve
    , solveQFFormula
    , solveQFLA
    ) where

import Control.Monad
import Data.List
import Data.Maybe
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Data.VectorSpace hiding (project)

import ToySolver.Data.ArithRel
import ToySolver.Data.Boolean
import qualified ToySolver.Data.LA as LA
import ToySolver.Data.Var
import qualified ToySolver.FourierMotzkin as FM
import qualified ToySolver.FourierMotzkin.Core as FM

-- ---------------------------------------------------------------------------

-- | Linear arithmetic expression over integers.
type ExprZ = LA.Expr Integer

fromLAAtom :: LA.Atom Rational -> QFFormula
fromLAAtom (ArithRel a op b) = arithRel op a' b'
  where
    (e1,c1) = FM.toRat a
    (e2,c2) = FM.toRat b
    a' = c2 *^ e1
    b' = c1 *^ e2

leZ, ltZ, geZ, gtZ :: ExprZ -> ExprZ -> Lit
leZ e1 e2 = e1 `ltZ` (e2 ^+^ LA.constant 1)
ltZ e1 e2 = Pos $ (e2 ^-^ e1)
geZ = flip leZ
gtZ = flip gtZ

eqZ :: ExprZ -> ExprZ -> QFFormula
eqZ e1 e2 = Lit (e1 `leZ` e2) .&&. Lit (e1 `geZ` e2)

-- | Literal
-- 
-- * @Pos e@ means @e > 0@
-- 
-- * @Divisible True d e@ means @e@ can be divided by @d@ (i.e. @d|e@)
-- 
-- * @Divisible False d e@ means @e@ can not be divided by @d@ (i.e. @¬(d|e)@)
data Lit
    = Pos ExprZ
    | Divisible Bool Integer ExprZ
    deriving (Show, Eq, Ord)

instance Variables Lit where
  vars (Pos t) = vars t
  vars (Divisible _ _ t) = vars t

instance Complement Lit where
  notB (Pos e) = e `leZ` LA.constant 0
  notB (Divisible b c e) = Divisible (not b) c e

-- | quantifier-free negation normal form
data QFFormula
    = T
    | F
    | And QFFormula QFFormula
    | Or QFFormula QFFormula
    | Lit Lit
    deriving (Show, Eq, Ord)

instance Complement QFFormula where
  notB T = false
  notB F = true
  notB (And a b) = notB a .||. notB b
  notB (Or a b) = notB a .&&. notB b
  notB (Lit lit) = Lit (notB lit)

instance MonotoneBoolean QFFormula where
  true  = T
  false = F
  (.&&.) = And
  (.||.) = Or

instance Boolean QFFormula

instance Variables QFFormula where
  vars T = IS.empty
  vars F = IS.empty
  vars (And a b) = vars a `IS.union` vars b
  vars (Or a b)  = vars a `IS.union` vars b
  vars (Lit l)    = vars l

instance IsArithRel (LA.Expr Integer) QFFormula where
  arithRel op lhs rhs =
    case op of
      Le  -> Lit $ leZ lhs rhs
      Ge  -> Lit $ geZ lhs rhs
      Lt  -> Lit $ ltZ lhs rhs
      Gt  -> Lit $ gtZ lhs rhs
      Eql -> eqZ lhs rhs
      NEq -> notB $ arithRel Eql lhs rhs

(.|.) :: Integer -> ExprZ -> QFFormula
n .|. e = Lit $ Divisible True n e

subst1 :: Var -> ExprZ -> QFFormula -> QFFormula
subst1 x e = go
  where
    go T = true
    go F = false
    go (And a b) =  go a .&&. go b
    go (Or a b) = go a .||. go b
    go (Lit (Divisible b c e1)) = Lit $ Divisible b c $ LA.applySubst1 x e e1
    go (Lit (Pos e1)) = Lit $ Pos $ LA.applySubst1 x e e1

simplify :: QFFormula -> QFFormula
simplify (And a b) = simplify1 $ simplify a .&&. simplify b
simplify (Or a b)  = simplify1 $ simplify a .||. simplify b
simplify formula   = simplify1 formula

simplify1 :: QFFormula -> QFFormula
simplify1 T = true
simplify1 F = false
simplify1 (And a b) =
  case (a, b) of
    (T, b') -> b'
    (a', T) -> a'
    (F, _) -> false
    (_, F) -> false
    (a',b') -> a' .&&. b'
simplify1 (Or a b) =
  case (a, b) of
    (F, b') -> b'
    (a', F) -> a'
    (T, _) -> true
    (_, T) -> true
    (a',b') -> a' .||. b'
simplify1 (Lit lit) = simplifyLit lit

simplifyLit :: Lit -> QFFormula
simplifyLit (Pos e) =
  case LA.asConst e of
    Just c -> if c > 0 then true else false
    Nothing ->
      -- e > 0  <=>  e - 1 >= 0
      -- <=>  LA.mapCoeff (`div` d) (e - 1) >= 0
      -- <=>  LA.mapCoeff (`div` d) (e - 1) + 1 > 0
      Lit $ Pos $ LA.mapCoeff (`div` d) e1 ^+^ LA.constant 1
  where
    e1 = e ^-^ LA.constant 1
    d  = if null cs then 1 else abs $ foldl1' gcd cs
    cs = [c | (c,x) <- LA.terms e1, x /= LA.unitVar]
simplifyLit lit@(Divisible b c e)
  | LA.coeff LA.unitVar e `mod` d /= 0 = if b then false else true
  | c' == 1   = if b then true else false
  | d  == 1   = Lit lit
  | otherwise = Lit $ Divisible b c' e'
  where
    d  = abs $ foldl' gcd c [c2 | (c2,x) <- LA.terms e, x /= LA.unitVar]
    c' = c `div` d
    e' = LA.mapCoeff (`div` d) e

evalQFFormula :: Model Integer -> QFFormula -> Bool
evalQFFormula m = f
  where
    f T = True
    f F = False
    f (And x1 x2) = f x1 && f x2
    f (Or  x1 x2) = f x1 || f x2
    f (Lit lit)    = evalLit m lit

evalLit :: Model Integer -> Lit -> Bool
evalLit m (Pos e) = LA.evalExpr m e > 0
evalLit m (Divisible True n e)  = LA.evalExpr m e `mod` n == 0
evalLit m (Divisible False n e) = LA.evalExpr m e `mod` n /= 0

-- ---------------------------------------------------------------------------

data Witness = WCase1 Integer ExprZ | WCase2 Integer Integer Integer [ExprZ]

evalWitness :: Model Integer -> Witness -> Integer
evalWitness model (WCase1 c e) = LA.evalExpr model e `div` c
evalWitness model (WCase2 c j delta us)
  | null us'  = j `div` c
  | otherwise = (j + (((u - delta - 1) `div` delta) * delta)) `div` c
  where
    us' = map (LA.evalExpr model) us
    u = minimum us'

-- ---------------------------------------------------------------------------

project :: Var -> QFFormula -> (QFFormula, Model Integer -> Model Integer)
project x formula = (formula', mt)
  where
    xs = projectCases x formula
    formula' = simplify $ orB [phi | (phi,_) <- xs, phi /= F]
    mt m = head $ do
      (phi, mt') <- xs
      guard $ evalQFFormula m phi
      return $ mt' m

projectN :: VarSet -> QFFormula -> (QFFormula, Model Integer -> Model Integer)
projectN vs2 = f (IS.toList vs2)
  where
    f :: [Var] -> QFFormula -> (QFFormula, Model Integer -> Model Integer)
    f [] formula     = (formula, id)
    f (v:vs) formula = (formula3, mt1 . mt2)
      where
        (formula2, mt1) = project v formula
        (formula3, mt2) = f vs formula2

projectCases :: Var -> QFFormula -> [(QFFormula, Model Integer -> Model Integer)]
projectCases x formula = do
  (phi, wit) <- projectCases' x formula
  return (phi, \m -> IM.insert x (evalWitness m wit) m)

projectCases' :: Var -> QFFormula -> [(QFFormula, Witness)]
projectCases' x formula = [(simplify phi, w) | (phi,w) <- case1 ++ case2]
  where
    -- xの係数の最小公倍数
    c :: Integer
    c = f formula
      where
         f :: QFFormula -> Integer
         f T = 1
         f F = 1
         f (And a b) = lcm (f a) (f b)
         f (Or a b) = lcm (f a) (f b)
         f (Lit (Pos e)) = fromMaybe 1 (LA.lookupCoeff x e)
         f (Lit (Divisible _ _ e)) = fromMaybe 1 (LA.lookupCoeff x e)
    
    -- 式をスケールしてxの係数の絶対値をcへと変換し、その後cxをxで置き換え、
    -- xがcで割り切れるという制約を追加した論理式
    formula1 :: QFFormula
    formula1 = simplify $ f formula .&&. Lit (Divisible True c (LA.var x))
      where
        f :: QFFormula -> QFFormula
        f T = T
        f F = F
        f (And a b) = f a .&&. f b
        f (Or a b) = f a .||. f b
        f lit@(Lit (Pos e)) =
          case LA.lookupCoeff x e of
            Nothing -> lit
            Just a ->
              let s = abs (c `div` a)
              in Lit $ Pos $ g s e
        f lit@(Lit (Divisible b d e)) =
          case LA.lookupCoeff x e of
            Nothing -> lit
            Just a ->
              let s = abs (c `div` a)
              in Lit $ Divisible b (s*d) $ g s e

        g :: Integer -> ExprZ -> ExprZ
        g s = LA.mapCoeffWithVar (\c' x' -> if x==x' then signum c' else s*c')

    -- d|x+t という形の論理式の d の最小公倍数
    delta :: Integer
    delta = f formula1
      where
        f :: QFFormula -> Integer
        f T = 1
        f F = 1
        f (And a b) = lcm (f a) (f b)
        f (Or a b)  = lcm (f a) (f b)
        f (Lit (Divisible _ d _)) = d
        f (Lit (Pos _)) = 1

    -- ts = {t | t < x は formula1 に現れる原子論理式}
    ts :: [ExprZ]
    ts = f formula1
      where
        f :: QFFormula -> [ExprZ]
        f T = []
        f F = []
        f (And a b) = f a ++ f b
        f (Or a b) = f a ++ f b
        f (Lit (Divisible _ _ _)) = []
        f (Lit (Pos e)) =
          case LA.extractMaybe x e of
            Nothing -> []
            Just (1, e')  -> [negateV e'] -- Pos e <=> (x + e' > 0) <=> (-e' < x)
            Just (-1, _) -> [] -- Pos e <=> (-x + e' > 0) <=> (x < e')
            _ -> error "should not happen"

    -- formula1を真にする最小のxが存在する場合
    case1 :: [(QFFormula, Witness)]
    case1 = [ (subst1 x e formula1, WCase1 c e)
            | j <- [1..delta], t <- ts, let e = t ^+^ LA.constant j ]

    -- formula1のなかの x < t を真に t < x を偽に置き換えた論理式
    formula2 :: QFFormula
    formula2 = simplify $ f formula1
      where        
        f :: QFFormula -> QFFormula
        f T = T
        f F = F
        f (And a b) = f a .&&. f b
        f (Or a b) = f a .||. f b
        f lit@(Lit (Pos e)) =
          case LA.lookupCoeff x e of
            Nothing -> lit
            Just 1    -> F -- Pos e <=> ( x + e' > 0) <=> -e' < x
            Just (-1) -> T -- Pos e <=> (-x + e' > 0) <=>  x  < e'
            _ -> error "should not happen"
        f lit@(Lit (Divisible _ _ _)) = lit

    -- us = {u | x < u は formula1 に現れる原子論理式}
    us :: [ExprZ]
    us = f formula1
      where
        f :: QFFormula -> [ExprZ]
        f T = []
        f F = []
        f (And a b) = f a ++ f b
        f (Or a b) = f a ++ f b
        f (Lit (Pos e)) =
          case LA.extractMaybe x e of
            Nothing -> []
            Just (1, _)   -> []   -- Pos e <=> ( x + e' > 0) <=> -e' < x
            Just (-1, e') -> [e'] -- Pos e <=> (-x + e' > 0) <=>  x  < e'
            _ -> error "should not happen"
        f (Lit (Divisible _ _ _)) = []

    -- formula1を真にする最小のxが存在しない場合
    case2 :: [(QFFormula, Witness)]
    case2 = [(subst1 x (LA.constant j) formula2, WCase2 c j delta us) | j <- [1..delta]]

projectCasesN :: VarSet -> QFFormula -> [(QFFormula, Model Integer -> Model Integer)]
projectCasesN vs2 = f (IS.toList vs2)
  where
    f :: [Var] -> QFFormula -> [(QFFormula, Model Integer -> Model Integer)]
    f [] formula = return (formula, id)
    f (v:vs) formula = do
      (formula2, mt1) <- projectCases v formula
      (formula3, mt2) <- f vs formula2
      return (formula3, mt1 . mt2)

-- ---------------------------------------------------------------------------

solveQFFormula :: VarSet -> QFFormula -> Maybe (Model Integer)
solveQFFormula vs formula = listToMaybe $ do
  (formula2, mt) <- projectCasesN vs formula
  case formula2 of
    T -> return $ mt IM.empty
    _  -> mzero

-- | solve a (open) quantifier-free formula
solve :: VarSet -> [LA.Atom Rational] -> Maybe (Model Integer)
solve vs cs = solveQFFormula vs $ andB $ map fromLAAtom cs

-- | solve a (open) quantifier-free formula
solveQFLA :: VarSet -> [LA.Atom Rational] -> VarSet -> Maybe (Model Rational)
solveQFLA vs cs ivs = listToMaybe $ do
  (cs2, mt) <- FM.projectN rvs cs
  m <- maybeToList $ solve ivs cs2
  return $ mt $ IM.map fromInteger m
  where
    rvs = vs `IS.difference` ivs

-- ---------------------------------------------------------------------------

testHagiya :: QFFormula
testHagiya = fst $ project 1 $ andB [c1, c2, c3]
  where
    [x,y,z] = map LA.var [1..3]
    c1 = x .<. (y ^+^ y)
    c2 = z .<. x
    c3 = 3 .|. x

{-
∃ x. 0 < y+y ∧ z<x ∧ 3|x
⇔
(2y-z > 0 ∧ 3|z+1) ∨ (2y-z > -2 ∧ 3|z+2) ∨ (2y-z > -3 ∧ 3|z+3)
-}

test3 :: QFFormula
test3 = fst $ project 1 $ andB [p1,p2,p3,p4]
  where
    x = LA.var 0
    y = LA.var 1
    p1 = LA.constant 0 .<. y
    p2 = 2 *^ x .<. y
    p3 = y .<. x ^+^ LA.constant 2
    p4 = 2 .|. y

{-
∃ y. 0 < y ∧ 2x<y ∧ y < x+2 ∧ 2|y
⇔
(2x < 2 ∧ 0 < x) ∨ (0 < 2x+2 ∧ x < 0)
-}

-- ---------------------------------------------------------------------------
