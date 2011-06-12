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
    ( Var
    , Term (..)
    , RelOp (..)
    , Formula (..)
    , Boolean (..)
    , andF, orF
    , (.+.), (.-.), (.*.)
    , (.<.), (.<=.), (.>=.), (.>.), (.==.), (./=.)
    , Tm (..)
    , Lit (..)
    , Formula' (..)
    , eliminateQuantifiers
    , solve
    , Model
    ) where

import Control.Monad
import Data.Maybe
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS

-- ---------------------------------------------------------------------------

-- | Variables are represented as non-negative integers
type Var = Int

class Variables a where
  vars :: a -> IS.IntSet

instance Variables a => Variables [a] where
  vars = IS.unions . map vars

type Model c = IM.IntMap c

-- ---------------------------------------------------------------------------

data Term c
    = Const c
    | Var Var
    | Add (Term c) (Term c)
    | Mul c (Term c)
    deriving (Show, Eq, Ord)

data RelOp = Lt | Le | Ge | Gt | Eql | NEq
    deriving (Show, Eq, Ord)

data Formula c
    = T
    | F
    | Rel (Term c) RelOp (Term c)
    | And (Formula c) (Formula c)
    | Or (Formula c) (Formula c)
    | Not (Formula c)
    | Imply (Formula c) (Formula c)
    | Equiv (Formula c) (Formula c)
    | Forall Var (Formula c)
    | Exists Var (Formula c)
    deriving (Show, Eq, Ord)

instance Variables (Term c) where
  vars (Const _) = IS.empty
  vars (Var v) = IS.singleton v
  vars (Add a b) = vars a `IS.union` vars b
  vars (Mul _ a) = vars a

instance Variables (Formula c) where
  vars T = IS.empty
  vars F = IS.empty
  vars (Rel a _ b) = vars a `IS.union` vars b
  vars (And a b) = vars a `IS.union` vars b
  vars (Or a b) = vars a `IS.union` vars b
  vars (Not a) = vars a
  vars (Imply a b) = vars a `IS.union` vars b
  vars (Equiv a b) = vars a `IS.union` vars b
  vars (Forall v a) = IS.delete v (vars a)
  vars (Exists v a) = IS.delete v (vars a)

pushNot :: Formula c -> Formula c
pushNot T = F
pushNot F = T
pushNot (Rel a op b) = Rel a op' b
  where
    op' = case op of
            Lt -> Ge
            Le -> Gt
            Ge -> Lt
            Gt -> Le
            Eql -> NEq
            NEq -> Eql
pushNot (And a b) = Or (pushNot a) (pushNot b)
pushNot (Or a b) = And (pushNot a) (pushNot b)
pushNot (Not a) = a
pushNot (Imply a b) = And a (pushNot b)
pushNot (Equiv a b) = Or (And a (pushNot b)) (And b (pushNot a))
pushNot (Forall v a) = Exists v (pushNot a)
pushNot (Exists v a) = Forall v (pushNot a)

-- ---------------------------------------------------------------------------
-- DSL

infixr 7 .*.
infixl 6 .+., .-.
infix 4 .<., .<=., .>=., .>., .==., ./=.
infixr 3 .&&.
infixr 2 .||.
infix 1 .=>. , .<=>.

class Boolean a where
  true, false :: a
  notF :: a -> a
  (.&&.), (.||.), (.=>.), (.<=>.) :: a -> a -> a
  x .=>. y = notF x .||. y
  x .<=>. y = (x .=>. y) .&&. (y .=>. x)

instance Boolean (Formula c) where
  true = T
  false = F
  notF = Not
  (.&&.) = And
  (.||.) = Or
  (.=>.) = Imply
  (.<=>.) = Equiv

andF :: Boolean a => [a] -> a
andF = foldr (.&&.) true

orF :: Boolean a => [a] -> a
orF = foldr (.||.) false

(.+.) :: Term c -> Term c -> Term c
(.+.) = Add

(.-.) :: Num c => Term c -> Term c -> Term c
a .-. b = a .+. (-1).*.b

(.*.) :: c -> Term c -> Term c
(.*.) = Mul

(.<.), (.<=.), (.>=.), (.>.), (.==.), (./=.) :: Term c -> Term c -> Formula c
a .<. b = Rel a Lt b
a .<=. b = Rel a Le b
a .>. b = Rel a Gt b
a .>=. b = Rel a Ge b
a .==. b = Rel a Eql b
a ./=. b = Rel a NEq b

-- ---------------------------------------------------------------------------

-- Linear combination of variables and constants.
-- Non-negative keys are used for variables's coefficients.
-- key '-1' is used for constants.
newtype Tm = Tm (IM.IntMap Integer) deriving (Eq, Ord, Show)

instance Variables Tm where
  vars (Tm t) = IS.delete (-1) $ IM.keysSet t

normalizeTm :: Tm -> Tm
normalizeTm (Tm t) = Tm $ IM.filter (0/=) t

constTm :: Integer -> Tm
constTm c = normalizeTm $ Tm $ IM.singleton (-1) c

varTm :: Var -> Tm
varTm v = Tm $ IM.singleton v 1

plusTm :: Tm -> Tm -> Tm
plusTm (Tm t1) (Tm t2) = normalizeTm $ Tm $ IM.unionWith (+) t1 t2

minusTm :: Tm -> Tm -> Tm
minusTm t1 t2 = t1 `plusTm` negateTm t2

scaleTm :: Integer -> Tm -> Tm
scaleTm c (Tm t) = normalizeTm $ Tm $ IM.map (c*) t

negateTm :: Tm -> Tm
negateTm = scaleTm (-1)

evalTm :: Model Integer -> Tm -> Integer
evalTm env (Tm t) = sum [(env' IM.! var) * c | (var,c) <- IM.toList t]
  where env' = IM.insert (-1) 1 env

termZ :: Term Integer -> Tm
termZ (Const c) = constTm c
termZ (Var v) = varTm v
termZ (Add t1 t2) =  termZ t1 `plusTm` termZ t2
termZ (Mul c t) = scaleTm c (termZ t)

atomZ :: RelOp -> Term Integer -> Term Integer -> Formula'
atomZ Le a b = Lit $ termZ a `leZ` termZ b
atomZ Lt a b = Lit $ termZ a `ltZ` termZ b
atomZ Ge a b = Lit $ termZ a `geZ` termZ b
atomZ Gt a b = Lit $ termZ a `gtZ` termZ b
atomZ Eql a b = eqZ (termZ a) (termZ b)
atomZ NEq a b = notF $ (atomZ Eql a b)

leZ, ltZ, geZ, gtZ :: Tm -> Tm -> Lit
leZ tm1 tm2 = tm1 `ltZ` (tm2 `plusTm` constTm 1)
ltZ tm1 tm2 = Pos $ (tm2 `minusTm` tm1)
geZ = flip leZ
gtZ = flip gtZ

eqZ :: Tm -> Tm -> Formula'
eqZ tm1 tm2 = Lit (tm1 `leZ` tm2) .&&. Lit (tm1 `geZ` tm2)

-- | Literal
data Lit
    = Pos Tm
    | Divisible Bool Integer Tm 
    deriving (Show, Eq, Ord)

instance Variables Lit where
  vars (Pos t) = vars t
  vars (Divisible _ _ t) = vars t

data Formula'
    = T'
    | F'
    | And' Formula' Formula'
    | Or' Formula' Formula'
    | Lit Lit
    deriving (Show, Eq, Ord)

instance Boolean Formula' where
  true = T'
  false = F'
  notF T' = F'
  notF F' = T'
  notF (And' a b) = Or' (notF a) (notF b)
  notF (Or' a b) = And' (notF a) (notF b)
  notF (Lit lit) = Lit (notLit lit)
  (.&&.) = And'
  (.||.) = Or'

notLit :: Lit -> Lit
notLit (Pos tm) = tm `leZ` constTm 0
notLit (Divisible b c tm) = Divisible (not b) c tm

subst1 :: Var -> Tm -> Formula' -> Formula'
subst1 x tm = go
  where
    go T' = T'
    go F' = F'
    go (And' a b) = And' (go a) (go b)
    go (Or' a b) = Or' (go a) (go b)
    go (Lit (Divisible b c tm1)) = Lit $ Divisible b c $ subst1' x tm tm1
    go (Lit (Pos tm1)) = Lit $ Pos $ subst1' x tm tm1

subst1' :: Var -> Tm -> Tm -> Tm
subst1' x tm tm1@(Tm m) =
  case IM.lookup x m of
    Nothing -> tm1
    Just c -> scaleTm c tm `plusTm` Tm (IM.delete x m)

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
simplify lit@(Lit (Pos tm)) =
  case asConst tm of
    Nothing -> lit
    Just c -> if c > 0 then true else false
simplify lit@(Lit (Divisible b c tm@(Tm m))) = 
  case asConst tm of
    Just c' ->
      if b == (c' `mod` c == 0) then true else false
    Nothing
      | c==d -> if b then true else false
      | d==1 -> lit
      | otherwise -> Lit (Divisible b (c `div` d) (Tm (IM.map (`div` d) m)))
  where
    d = foldl gcd c (IM.elems m)

asConst :: Tm -> Maybe Integer
asConst (Tm tm) =
  case IM.toList tm of
    [] -> Just 0
    [(-1,x)] -> Just x
    _ -> Nothing

-- ---------------------------------------------------------------------------

data Witness = WCase1 Integer Tm | WCase2 Integer Integer Integer [Tm]

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
         f (Lit (Pos (Tm m))) = fromMaybe 1 (IM.lookup x m)
         f (Lit (Divisible _ _ (Tm m))) = fromMaybe 1 (IM.lookup x m)
    
    formula1 :: Formula'
    formula1 = f formula .&&. Lit (Divisible True c (varTm x))
      where
        f :: Formula' -> Formula'
        f T' = T'
        f F' = F'
        f (And' a b) = f a .&&. f b
        f (Or' a b) = f a .||. f b
        f lit@(Lit (Pos (Tm m))) =
          case IM.lookup x m of
            Nothing -> lit
            Just a ->
              let e = c `div` abs a
              in Lit $ Pos $ Tm $ IM.mapWithKey (\x' c' -> if x==x' then signum c' else e*c') m
        f lit@(Lit (Divisible b d (Tm m))) =
          case IM.lookup x m of
            Nothing -> lit
            Just a ->
              let e = c `div` abs a
              in Lit $ Divisible b (e*d) $ Tm $ IM.mapWithKey (\x' c' -> if x==x' then signum c' else e*c') m

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

    bs :: [Tm]
    bs = f formula1
      where
        f :: Formula' -> [Tm]
        f T' = []
        f F' = []
        f (And' a b) = f a ++ f b
        f (Or' a b) = f a ++ f b
        f (Lit (Divisible _ _ _)) = []
        f (Lit (Pos (Tm m))) =
            case IM.lookup x m of
              Nothing -> []
              Just c' -> if c' > 0 then [negateTm (Tm (IM.delete x m))] else [Tm (IM.delete x m)]    

    case1 :: [(Formula', Witness)]
    case1 = [ (subst1 x tm formula1, WCase1 c tm)
            | j <- [1..delta], b <- bs, let tm = b `plusTm` constTm j ]

    p :: Formula'
    p = f formula1
      where        
        f :: Formula' -> Formula'
        f T' = T'
        f F' = F'
        f (And' a b) = f a .&&. f b
        f (Or' a b) = f a .||. f b
        f lit@(Lit (Pos (Tm m))) =
          case IM.lookup x m of
            Nothing -> lit
            Just c -> if c < 0 then T' else F'
        f lit@(Lit (Divisible _ _ _)) = lit

    us :: [Tm]
    us = f formula1
      where
        f :: Formula' -> [Tm]
        f T' = []
        f F' = []
        f (And' a b) = f a ++ f b
        f (Or' a b) = f a ++ f b
        f (Lit (Pos (Tm m))) =
          case IM.lookup x m of
            Nothing -> []
            Just c -> if c < 0 then [Tm (IM.delete x m)] else []
        f (Lit (Divisible _ _ _)) = []

    case2 :: [(Formula', Witness)]
    case2 = [(subst1 x (constTm j) p, WCase2 c j delta us) | j <- [1..delta]]

evalWitness :: Model Integer -> Witness -> Integer
evalWitness model (WCase1 c tm) = evalTm model tm `div` c
evalWitness model (WCase2 c j delta us)
  | null us' = j `div` c
  | otherwise = (j + (((u - delta - 1) `div` delta) * delta)) `div` c
  where
    us' = map (evalTm model) us
    u = minimum us'

-- ---------------------------------------------------------------------------

eliminateQuantifiers :: Formula Integer -> Formula'
eliminateQuantifiers = f
  where
    f T = T'
    f F = F'
    f (Rel tm1 op tm2) = atomZ op tm1 tm2
    f (And a b) = f a .&&. f b
    f (Or a b) = f a .||. f b
    f (Not a) = f (pushNot a)
    f (Imply a b) = f $ Or (Not a) b
    f (Equiv a b) = f $ And (Imply a b) (Imply b a)
    f (Forall x body) = notF $ f $ Exists x $ pushNot body
    f (Exists x body) = eliminateZ x (f body)

-- ---------------------------------------------------------------------------

solve :: Formula Integer -> Maybe (Model Integer)
solve formula = solve' vs formula'
  where
    formula' = eliminateQuantifiers formula
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

{-
7x + 12y + 31z = 17
3x + 5y + 14z = 7
1 ≤ x ≤ 40
-50 ≤ y ≤ 50

satisfiable in R
but unsatisfiable in Z
-}
test1 :: Num c => Formula c
test1 = c1 .&&. c2 .&&. c3 .&&. c4
  where
    x = Var 0
    y = Var 1
    z = Var 2
    c1 = 7.*.x .+. 12.*.y .+. 31.*.z .==. Const 17
    c2 = 3.*.x .+. 5.*.y .+. 14.*.z .==. Const 7
    c3 = Const 1 .<=. x .&&. x .<=. Const 40
    c4 = Const (-50) .<=. y .&&. y .<=. Const 50

{-
27 ≤ 11x+13y ≤ 45
-10 ≤ 7x-9y ≤ 4

satisfiable in R
but unsatisfiable in Z
-}
test2 :: Num c => Formula c
test2 = c1 .&&. c2
  where
    x = Var 0
    y = Var 1
    t1 = 11.*.x .+. 13.*.y
    t2 = 7.*.x .-. 9.*.y
    c1 = Const 27 .<=. t1 .&&. t1 .<=. Const 45
    c2 = Const (-10) .<=. t2 .&&. t2 .<=. Const 4

-- ---------------------------------------------------------------------------
