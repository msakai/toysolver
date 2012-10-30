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
module Cooper
    ( module Data.Expr
    , module Data.Formula
    , ExprZ
    , Lit (..)
    , Formula' (..)
    , eliminateQuantifiers
    , solve
    , solveConj
    , solveQFLA
    , Model
    ) where

import Control.Monad
import Data.List
import Data.Maybe
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS

import Data.Expr
import Data.Formula
import Data.Linear
import qualified Data.LA as LA
import qualified FourierMotzkin as FM
import qualified Data.Interval as Interval

-- ---------------------------------------------------------------------------

-- | Linear arithmetic expression over integers.
type ExprZ = LA.Expr Integer

atomZ :: RelOp -> Expr Rational -> Expr Rational -> Maybe Formula'
atomZ op a b = do
  (e1,c1) <- FM.termR a
  (e2,c2) <- FM.termR b
  let a' = c2 .*. e1
      b' = c1 .*. e2
  case op of
    Le -> return $ Lit $ a' `leZ` b'
    Lt -> return $ Lit $ a' `ltZ` b'
    Ge -> return $ Lit $ a' `geZ` b'
    Gt -> return $ Lit $ a' `gtZ` b'
    Eql -> return $ eqZ a' b'
    NEq -> liftM notB (atomZ Eql a b)

leZ, ltZ, geZ, gtZ :: ExprZ -> ExprZ -> Lit
leZ e1 e2 = e1 `ltZ` (e2 .+. LA.constant 1)
ltZ e1 e2 = Pos $ (e2 .-. e1)
geZ = flip leZ
gtZ = flip gtZ

eqZ :: ExprZ -> ExprZ -> Formula'
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
data Formula'
    = T'
    | F'
    | And' Formula' Formula'
    | Or' Formula' Formula'
    | Lit Lit
    deriving (Show, Eq, Ord)

instance Complement Formula' where
  notB T' = F'
  notB F' = T'
  notB (And' a b) = Or' (notB a) (notB b)
  notB (Or' a b) = And' (notB a) (notB b)
  notB (Lit lit) = Lit (notB lit)

instance Lattice Formula' where
  top    = T'
  bottom = F'
  meet   = And'
  join   = Or'

instance Boolean Formula'

subst1 :: Var -> ExprZ -> Formula' -> Formula'
subst1 x e = go
  where
    go T' = T'
    go F' = F'
    go (And' a b) = And' (go a) (go b)
    go (Or' a b) = Or' (go a) (go b)
    go (Lit (Divisible b c e1)) = Lit $ Divisible b c $ LA.applySubst1 x e e1
    go (Lit (Pos e1)) = Lit $ Pos $ LA.applySubst1 x e e1

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
simplify (Lit lit) = simplifyLit lit

simplifyLit :: Lit -> Formula'
simplifyLit (Pos e) =
  case LA.asConst e of
    Just c -> if c > 0 then true else false
    Nothing ->
      -- e > 0  <=>  e - 1 >= 0
      -- <=>  LA.mapCoeff (`div` d) (e - 1) >= 0
      -- <=>  LA.mapCoeff (`div` d) (e - 1) + 1 > 0
      Lit $ Pos $ LA.mapCoeff (`div` d) (e .-. LA.constant 1) .+. LA.constant 1
  where
    d = if null cs then 1 else abs $ foldl1' gcd cs
    cs = [c | (c,x) <- LA.terms e, x /= LA.unitVar]
simplifyLit lit@(Divisible b c e)
  | LA.coeff LA.unitVar e `mod` d /= 0 = if b then false else true
  | c' == 1   = if b then true else false
  | d  == 1   = Lit lit
  | otherwise = Lit $ Divisible b c' e'
  where
    d  = abs $ foldl' gcd c [c2 | (c2,x) <- LA.terms e, x /= LA.unitVar]
    c' = c `div` d
    e' = LA.mapCoeff (`div` d) e

-- ---------------------------------------------------------------------------

data Witness = WCase1 Integer ExprZ | WCase2 Integer Integer Integer [ExprZ]

eliminateZ :: Var -> Formula' -> Formula'
eliminateZ x formula = simplify $ orB $ map fst $ eliminateZ' x formula

eliminateZ' :: Var -> Formula' -> [(Formula', Witness)]
eliminateZ' x formula = case1 ++ case2
  where
    -- xの係数の最小公倍数
    c :: Integer
    c = f formula
      where
         f :: Formula' -> Integer
         f T' = 1
         f F' = 1
         f (And' a b) = lcm (f a) (f b)
         f (Or' a b) = lcm (f a) (f b)
         f (Lit (Pos e)) = fromMaybe 1 (LA.lookupCoeff x e)
         f (Lit (Divisible _ _ e)) = fromMaybe 1 (LA.lookupCoeff x e)
    
    -- 式をスケールしてxの係数の絶対値をcへと変換し、その後cxをxで置き換え、
    -- xがcで割り切れるという制約を追加した論理式
    formula1 :: Formula'
    formula1 = simplify $ f formula .&&. Lit (Divisible True c (LA.var x))
      where
        f :: Formula' -> Formula'
        f T' = T'
        f F' = F'
        f (And' a b) = f a .&&. f b
        f (Or' a b) = f a .||. f b
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
        f :: Formula' -> Integer
        f T' = 1
        f F' = 1
        f (And' a b) = lcm (f a) (f b)
        f (Or' a b)  = lcm (f a) (f b)
        f (Lit (Divisible _ d _)) = d
        f (Lit (Pos _)) = 1

    -- ts = {t | t < x は formula1 に現れる原子論理式}
    ts :: [ExprZ]
    ts = f formula1
      where
        f :: Formula' -> [ExprZ]
        f T' = []
        f F' = []
        f (And' a b) = f a ++ f b
        f (Or' a b) = f a ++ f b
        f (Lit (Divisible _ _ _)) = []
        f (Lit (Pos e)) =
          case LA.extractMaybe x e of
            Nothing -> []
            Just (1, e')  -> [lnegate e'] -- Pos e <=> (x + e' > 0) <=> (-e' < x)
            Just (-1, _) -> [] -- Pos e <=> (-x + e' > 0) <=> (x < e')
            _ -> error "should not happen"

    -- formula1を真にする最小のxが存在する場合
    case1 :: [(Formula', Witness)]
    case1 = [ (subst1 x e formula1, WCase1 c e)
            | j <- [1..delta], t <- ts, let e = t .+. LA.constant j ]

    -- formula1のなかの x < t を真に t < x を偽に置き換えた論理式
    formula2 :: Formula'
    formula2 = simplify $ f formula1
      where        
        f :: Formula' -> Formula'
        f T' = T'
        f F' = F'
        f (And' a b) = f a .&&. f b
        f (Or' a b) = f a .||. f b
        f lit@(Lit (Pos e)) =
          case LA.lookupCoeff x e of
            Nothing -> lit
            Just 1    -> F' -- Pos e <=> ( x + e' > 0) <=> -e' < x
            Just (-1) -> T' -- Pos e <=> (-x + e' > 0) <=>  x  < e'
            _ -> error "should not happen"
        f lit@(Lit (Divisible _ _ _)) = lit

    -- us = {u | x < u は formula1 に現れる原子論理式}
    us :: [ExprZ]
    us = f formula1
      where
        f :: Formula' -> [ExprZ]
        f T' = []
        f F' = []
        f (And' a b) = f a ++ f b
        f (Or' a b) = f a ++ f b
        f (Lit (Pos e)) =
          case LA.extractMaybe x e of
            Nothing -> []
            Just (1, _)   -> []   -- Pos e <=> ( x + e' > 0) <=> -e' < x
            Just (-1, e') -> [e'] -- Pos e <=> (-x + e' > 0) <=>  x  < e'
            _ -> error "should not happen"
        f (Lit (Divisible _ _ _)) = []

    -- formula1を真にする最小のxが存在しない場合
    case2 :: [(Formula', Witness)]
    case2 = [(subst1 x (LA.constant j) formula2, WCase2 c j delta us) | j <- [1..delta]]

evalWitness :: Model Integer -> Witness -> Integer
evalWitness model (WCase1 c e) = LA.evalExpr model e `div` c
evalWitness model (WCase2 c j delta us)
  | null us'  = j `div` c
  | otherwise = (j + (((u - delta - 1) `div` delta) * delta)) `div` c
  where
    us' = map (LA.evalExpr model) us
    u = minimum us'

-- ---------------------------------------------------------------------------

-- | eliminate quantifiers and returns equivalent quantifier-free formula.
eliminateQuantifiers :: Formula (Atom Rational) -> Maybe Formula'
eliminateQuantifiers = f
  where
    f T = return T'
    f F = return F'
    f (Atom (Rel e1 op e2)) = atomZ op e1 e2
    f (And a b) = liftM2 (.&&.) (f a) (f b)
    f (Or a b) = liftM2 (.||.) (f a) (f b)
    f (Not a) = f (pushNot a)
    f (Imply a b) = f $ Or (Not a) b
    f (Equiv a b) = f $ And (Imply a b) (Imply b a)
    f (Forall x body) = liftM notB $ f $ Exists x $ pushNot body
    f (Exists x body) = liftM (eliminateZ x) (f body)

-- ---------------------------------------------------------------------------

-- | solve a formula and returns assignment of outer-most existential quantified
-- variables.
solve :: Formula (Atom Rational) -> SatResult Integer
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
solve' vs2 formula2 = go vs2 (simplify formula2)
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

solveConj :: [LA.Atom Rational] -> Maybe (Model Integer)
solveConj cs = msum [ solve' vs (foldr And' T' (map f xs)) | xs <- unDNF dnf ]
  where
    dnf = FM.constraintsToDNF cs
    vs = IS.toList (vars cs)

    f :: FM.Lit -> Formula'
    f (FM.Nonneg e) = Lit $ e `geZ` LA.constant 0
    f (FM.Pos e)    = Lit $ e `gtZ` LA.constant 0

-- | solve a (open) quantifier-free formula
solveQFLA :: [LA.Atom Rational] -> VarSet -> Maybe (Model Rational)
solveQFLA cs ivs = msum [ FM.simplify xs >>= go (IS.toList rvs) | xs <- unDNF dnf ]
  where
    rvs = vars cs `IS.difference` ivs
    dnf = FM.constraintsToDNF cs

    go :: [Var] -> [FM.Lit] -> Maybe (Model Rational)
    go [] xs = fmap (fmap fromIntegral) $ solve' (IS.toList ivs) (foldr And' T' (map f xs))
    go (v:vs) ys = msum $ map g $ unDNF $ FM.boundConditions bnd
      where
        (bnd, rest) = FM.collectBounds v ys
        g zs = do
          model <- go vs (zs ++ rest)
          val <- Interval.pickup (FM.evalBounds model bnd)
          return $ IM.insert v val model

    f :: FM.Lit -> Formula'
    f (FM.Nonneg e) = Lit $ e `geZ` LA.constant 0
    f (FM.Pos e)    = Lit $ e `gtZ` LA.constant 0

-- ---------------------------------------------------------------------------

testHagiya :: Formula'
testHagiya = eliminateZ 1 $ c1 .&&. c2 .&&. c3
  where
    [x,y,z] = map LA.var [1..3]
    c1 = Lit $ x `ltZ` (y .+. y)   -- x < y+y
    c2 = Lit $ z `ltZ` x           -- z < x
    c3 = Lit $ Divisible True 3 x  -- 3 | x

{-
Or' (And' (Lit (Pos (Expr {coeffMap = fromList [(-1,-1),(2,2),(3,-1)]}))) (Lit (Divisible True 3 (Expr {coeffMap = fromList [(-1,1),(3,1)]}))))
    (Or' (And' (Lit (Pos (Expr {coeffMap = fromList [(-1,-2),(2,2),(3,-1)]}))) (Lit (Divisible True 3 (Expr {coeffMap = fromList [(-1,2),(3,1)]}))))
         (And' (Lit (Pos (Expr {coeffMap = fromList [(-1,-3),(2,2),(3,-1)]}))) (Lit (Divisible True 3 (Expr {coeffMap = fromList [(-1,3),(3,1)]})))))

(2y-z >  0 && 3|z+1) ||
(2y-z > -2 && 3|z+2) ||
(2y-z > -3 && 3|z+3) ||
-}

test3 :: Formula'
test3 = eliminateZ 1 (andB [p1,p2,p3,p4])
  where
    x = LA.var 0
    y = LA.var 1
    p1 = Lit $ Pos y
    p2 = Lit $ Pos (y .-. 2 .*. x)
    p3 = Lit $ Pos (x .+. LA.constant 2 .-. y)
    p4 = Lit $ Divisible True 2 y

{-
∃ y. 0 < y ∧ 2x<y ∧ y < x+2 ∧ 2|y
⇔
(2x < 2 ∧ 0 < x) ∨ (0 < 2x+2 ∧ x < 0)
-}

-- ---------------------------------------------------------------------------
