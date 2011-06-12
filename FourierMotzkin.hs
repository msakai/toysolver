{-# OPTIONS_GHC -Wall #-}
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
    , DNF (..)
    , eliminateQuantifiersR
    , eliminateQuantifiersZ
    , solveR
    , solveZ
    , Model
    ) where

import Control.Monad
import Data.List
import Data.Maybe
import Data.Ratio
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

-- | (t,c) represents t/c, and c must be >0.
type Rat = (Tm, Integer)

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
evalTm model (Tm t) = sum [(model' IM.! var) * c | (var,c) <- IM.toList t]
  where model' = IM.insert (-1) 1 model

evalRat :: Model Rational -> Rat -> Rational
evalRat model (Tm t, c1) = sum [(model' IM.! var) * (c % c1) | (var,c) <- IM.toList t]
  where model' = IM.insert (-1) 1 model

-- | Literal
data Lit = Nonneg Tm | Pos Tm deriving (Show, Eq, Ord)

instance Variables Lit where
  vars (Pos t) = vars t
  vars (Nonneg t) = vars t

-- | Disjunctive normal form
newtype DNF = DNF{ unDNF :: [[Lit]] }

instance Boolean DNF where
  true = DNF [[]]
  false = DNF []
  notF (DNF xs) = DNF . sequence . map (map f) $ xs
    where
      f :: Lit -> Lit
      f (Pos t) = Nonneg (negateTm t)
      f (Nonneg t) = Pos (negateTm t)
  DNF xs .&&. DNF ys = DNF [x++y | x<-xs, y<-ys]
  DNF xs .||. DNF ys = DNF (xs++ys)

-- 制約集合の単純化
-- It returns Nothing when a inconsistency is detected.
simplify :: [Lit] -> Maybe [Lit]
simplify = fmap concat . mapM f
  where
    f :: Lit -> Maybe [Lit]
    f lit@(Pos tm) =
      case g tm of
        Just x -> guard (x > 0) >> return []
        Nothing -> return [lit]
    f lit@(Nonneg tm) =
      case g tm of
        Just x -> guard (x >= 0) >> return []
        Nothing -> return [lit]

    g :: Tm -> Maybe Integer
    g (Tm tm) =
      case IM.toList tm of
        [] -> Just 0
        [(-1,x)] -> Just x
        _ -> Nothing

-- ---------------------------------------------------------------------------

atomR :: RelOp -> Term Rational -> Term Rational -> DNF
atomR Le a b = DNF [[termR a `leR` termR b]]
atomR Lt a b = DNF [[termR a `ltR` termR b]]
atomR Ge a b = DNF [[termR a `geR` termR b]]
atomR Gt a b = DNF [[termR a `gtR` termR b]]
atomR Eql a b = DNF [[termR a `leR` termR b, termR a `geR` termR b]]
atomR NEq a b = DNF [[termR a `ltR` termR b], [termR a `gtR` termR b]]

termR :: Term Rational -> Rat
termR (Const c) = (constTm (numerator c), denominator c)
termR (Var v) = (varTm v, 1)
termR (Add a b) =
  case (termR a, termR b) of
    ((t1,c1), (t2,c2)) ->
      (scaleTm c2 t1 `plusTm` scaleTm c1 t2, c1*c2)
termR (Mul c a) =
  case termR a of
    (t,c1) ->
      (scaleTm (numerator c) t, c1 * denominator c)

leR, ltR, geR, gtR :: Rat -> Rat -> Lit
leR (tm1,c) (tm2,d) = Nonneg $ normalizeTmR $ scaleTm c tm2 `minusTm` scaleTm d tm1
ltR (tm1,c) (tm2,d) = Pos $ normalizeTmR $ scaleTm c tm2 `minusTm` scaleTm d tm1
geR = flip leR
gtR = flip gtR

normalizeTmR :: Tm -> Tm
normalizeTmR (Tm m) = Tm (IM.map (`div` d) m)
  where d = gcd' $ map snd $ IM.toList m

-- ---------------------------------------------------------------------------

atomZ :: RelOp -> Term Integer -> Term Integer -> DNF
atomZ Le a b = DNF [[termZ a `leZ` termZ b]]
atomZ Lt a b = DNF [[termZ a `ltZ` termZ b]]
atomZ Ge a b = DNF [[termZ a `geZ` termZ b]]
atomZ Gt a b = DNF [[termZ a `gtZ` termZ b]]
atomZ Eql a b = eqZ (termZ a) (termZ b)
atomZ NEq a b = DNF [[termZ a `ltZ` termZ b], [termZ a `gtZ` termZ b]]

termZ :: Term Integer -> Tm
termZ (Const c) = constTm c
termZ (Var v) = varTm v
termZ (Add t1 t2) =  termZ t1 `plusTm` termZ t2
termZ (Mul c t) = scaleTm c (termZ t)

leZ, ltZ, geZ, gtZ :: Tm -> Tm -> Lit
-- Note that constants may be floored by division
leZ tm1 tm2 = Nonneg (Tm (IM.map (`div` d) m))
  where
    Tm m = tm2 `minusTm` tm1
    d = gcd' [c | (var,c) <- IM.toList m, var /= -1]
ltZ tm1 tm2 = (tm1 `plusTm` constTm 1) `leZ` tm2
geZ = flip leZ
gtZ = flip gtZ

eqZ :: Tm -> Tm -> DNF
eqZ tm1 tm2
  = if fromMaybe 0 (IM.lookup (-1) m) `mod` d == 0
    then DNF [[Nonneg tm, Nonneg (negateTm tm)]]
    else false
  where
    Tm m = tm1 `minusTm` tm2
    tm = Tm (IM.map (`div` d) m)
    d = gcd' [c | (var,c) <- IM.toList m, var /= -1]

-- ---------------------------------------------------------------------------

{-
(ls1,ls2,us1,us2) represents
{ x | ∀(M,c)∈ls1. M/c≤x, ∀(M,c)∈ls2. M/c<x, ∀(M,c)∈us1. x≤M/c, ∀(M,c)∈us2. x<M/c }
-}
type BoundsR = ([Rat], [Rat], [Rat], [Rat])

eliminateR :: Var -> [Lit] -> DNF
eliminateR v xs = DNF [rest] .&&. boundConditionsR bnd
  where
    (bnd, rest) = collectBoundsR v xs

collectBoundsR :: Var -> [Lit] -> (BoundsR, [Lit])
collectBoundsR v = foldr phi (([],[],[],[]),[])
  where
    phi :: Lit -> (BoundsR, [Lit]) -> (BoundsR, [Lit])
    phi lit@(Nonneg t) x = f False lit t x
    phi lit@(Pos t) x = f True lit t x

    f :: Bool -> Lit -> Tm -> (BoundsR, [Lit]) -> (BoundsR, [Lit])
    f strict lit (Tm t) (bnd@(ls1,ls2,us1,us2), xs) = 
      case c `compare` 0 of
        EQ -> (bnd, lit : xs)
        GT ->
          if strict
          then ((ls1, (negateTm t', c) : ls2, us1, us2), xs) -- 0 < cx + M ⇔ -M/c <  x
          else (((negateTm t', c) : ls1, ls2, us1, us2), xs) -- 0 ≤ cx + M ⇔ -M/c ≤ x
        LT -> 
          if strict
          then ((ls1, ls2, us1, (t', negate c) : us2), xs) -- 0 < cx + M ⇔ x < M/-c
          else ((ls1, ls2, (t', negate c) : us1, us2), xs) -- 0 ≤ cx + M ⇔ x ≤ M/-c
      where
        c = fromMaybe 0 $ IM.lookup v t
        t' = Tm $ IM.delete v t

boundConditionsR :: BoundsR -> DNF
boundConditionsR  (ls1, ls2, us1, us2) = DNF $ maybeToList $ simplify $ 
  [ x `leR` y | x <- ls1, y <- us1 ] ++
  [ x `ltR` y | x <- ls1, y <- us2 ] ++ 
  [ x `ltR` y | x <- ls2, y <- us1 ] ++
  [ x `ltR` y | x <- ls2, y <- us2 ]

eliminateQuantifiersR :: Formula Rational -> DNF
eliminateQuantifiersR = f
  where
    f T = true
    f F = false
    f (Rel a op b) = atomR op a b
    f (And a b) = f a .&&. f b
    f (Or a b) = f a .||. f b
    f (Not a) = f (pushNot a)
    f (Imply a b) = f (Or (Not a) b)
    f (Equiv a b) = f (And (Imply a b) (Imply b a))
    f (Forall v a) = notF $ f (Exists v (pushNot a))
    f (Exists v a) = orF [eliminateR v xs | xs <- unDNF (f a)]

solveR :: Formula Rational -> Maybe (Model Rational)
solveR formula = msum [solveR' vs xs | xs <- unDNF dnf]
  where
    dnf = eliminateQuantifiersR formula
    vs = IS.toList (vars formula)

solveR' :: [Var] -> [Lit] -> Maybe (Model Rational)
solveR' vs xs = simplify xs >>= go vs
  where
    go [] [] = return IM.empty
    go [] _ = mzero
    go (v:vs) ys = msum (map f (unDNF (boundConditionsR bnd)))
      where
        (bnd, rest) = collectBoundsR v ys
        f zs = do
          model <- go vs (zs ++ rest)
          val <- pickupR (evalBoundsR model bnd)
          return $ IM.insert v val model

evalBoundsR :: Model Rational -> BoundsR -> IntervalR
evalBoundsR model (ls1,ls2,us1,us2) =
  foldl' intersectR univR $ 
    [ (Just (True, evalRat model x), Nothing)  | x <- ls1 ] ++
    [ (Just (False, evalRat model x), Nothing) | x <- ls2 ] ++
    [ (Nothing, Just (True, evalRat model x))  | x <- us1 ] ++
    [ (Nothing, Just (False, evalRat model x)) | x <- us2 ]

-- ---------------------------------------------------------------------------

-- | Endpoint
-- (isInclusive, value)
type EP = Maybe (Bool, Rational)

type IntervalR = (EP, EP)

univR :: IntervalR
univR = (Nothing, Nothing)

intersectR :: IntervalR -> IntervalR -> IntervalR
intersectR (l1,u1) (l2,u2) = (maxEP l1 l2, minEP u1 u2)
  where 
    maxEP :: EP -> EP -> EP
    maxEP = combine $ \(in1,x1) (in2,x2) ->
      ( case x1 `compare` x2 of
          EQ -> in1 && in2
          LT -> in2
          GT -> in1
      , max x1 x2
      )

    minEP :: EP -> EP -> EP
    minEP = combine $ \(in1,x1) (in2,x2) ->
      ( case x1 `compare` x2 of
          EQ -> in1 && in2
          LT -> in1
          GT -> in2
      , min x1 x2
      )

pickupR :: IntervalR -> Maybe Rational
pickupR (Nothing,Nothing) = Just 0
pickupR (Just (in1,x1), Nothing) = Just $ if in1 then x1 else x1+1
pickupR (Nothing, Just (in2,x2)) = Just $ if in2 then x2 else x2-1
pickupR (Just (in1,x1), Just (in2,x2)) =
  case x1 `compare` x2 of
    GT -> Nothing
    LT -> Just $ (x1+x2) / 2
    EQ -> if in1 && in2 then Just x1 else Nothing

-- ---------------------------------------------------------------------------

{-
(ls,us) represents
{ x | ∀(M,c)∈ls. M/c≤x, ∀(M,c)∈us. x≤M/c }
-}
type BoundsZ = ([Rat],[Rat])

eliminateZ :: Var -> [Lit] -> DNF
eliminateZ v xs = DNF [rest] .&&. boundConditionsZ bnd
   where
     (bnd,rest) = collectBoundsZ v xs

collectBoundsZ :: Var -> [Lit] -> (BoundsZ,[Lit])
collectBoundsZ v = foldr phi (([],[]),[])
  where
    phi :: Lit -> (BoundsZ,[Lit]) -> (BoundsZ,[Lit])
    phi (Pos t) x = phi (Nonneg (t `minusTm` constTm 1)) x
    phi lit@(Nonneg (Tm t)) ((ls,us),xs) =
      case c `compare` 0 of
        EQ -> ((ls, us), lit : xs)
        GT -> (((negateTm t', c) : ls, us), xs) -- 0 ≤ cx + M ⇔ -M/c ≤ x
        LT -> ((ls, (t', negate c) : us), xs)   -- 0 ≤ cx + M ⇔ x ≤ M/-c
      where
        c = fromMaybe 0 $ IM.lookup v t
        t' = Tm $ IM.delete v t

boundConditionsZ :: BoundsZ -> DNF
boundConditionsZ (ls,us) = DNF $ catMaybes $ map simplify $ cond1 : cond2
  where
     cond1 =
       [ constTm ((a-1)*(b-1)) `leZ` (scaleTm a d `minusTm` scaleTm b c)
       | (c,a)<-ls , (d,b)<-us ]
     cond2 = 
       [ [scaleTm a' c `leZ` scaleTm a val | (c,a)<-ls] ++
         [scaleTm b val `geZ` scaleTm a' d | (d,b)<-us]
       | not (null us)
       , let m = maximum [b | (_,b)<-us]
       ,  (c',a') <- ls
       , k <- [0 .. (m*a'-a'-m) `div` m]
       , let val = c' `plusTm` constTm k
       -- x = val / a'
       -- c / a ≤ x ⇔ c / a ≤ val / a' ⇔ a' c ≤ a val
       -- x ≤ d / b ⇔ val / a' ≤ d / b ⇔ b val ≤ a' d
       ]

eliminateQuantifiersZ :: Formula Integer -> DNF
eliminateQuantifiersZ = f
  where
    f T = true
    f F = false
    f (Rel a op b) = atomZ op a b
    f (And a b) = f a .&&. f b
    f (Or a b) = f a .||. f b
    f (Not a) = f (pushNot a)
    f (Imply a b) = f (Or (Not a) b)
    f (Equiv a b) = f (And (Imply a b) (Imply b a))
    f (Forall v a) = notF $ f (Exists v (pushNot a))
    f (Exists v a) = orF [eliminateZ v xs | xs <- unDNF (f a)]

solveZ :: Formula Integer -> Maybe (Model Integer)
solveZ formula = msum [solveZ' vs xs | xs <- unDNF dnf]
  where
    dnf = eliminateQuantifiersZ formula
    vs = IS.toList (vars formula)

solveZ' :: [Var] -> [Lit] -> Maybe (Model Integer)
solveZ' vs xs = simplify xs >>= go vs
  where
    go :: [Var] -> [Lit] -> Maybe (Model Integer)
    go [] [] = return IM.empty
    go [] _ = mzero
    go (v:vs) ys = msum (map f (unDNF (boundConditionsZ bnd)))
      where
        (bnd, rest) = collectBoundsZ v ys
        f zs = do
          model <- go vs (zs ++ rest)
          val <- pickupZ (evalBoundsZ model bnd)
          return $ IM.insert v val model

evalBoundsZ :: Model Integer -> BoundsZ -> IntervalZ
evalBoundsZ model (ls,us) =
  foldl' intersectZ univZ $ 
    [ (Just (ceiling (evalTm model x % c)), Nothing) | (x,c) <- ls ] ++ 
    [ (Nothing, Just (floor (evalTm model x % c))) | (x,c) <- us ]

-- ---------------------------------------------------------------------------

type IntervalZ = (Maybe Integer, Maybe Integer)

univZ :: IntervalZ
univZ = (Nothing, Nothing)

intersectZ :: IntervalZ -> IntervalZ -> IntervalZ
intersectZ (l1,u1) (l2,u2) = (combine max l1 l2, combine min u1 u2)

pickupZ :: IntervalZ -> Maybe Integer
pickupZ (Nothing,Nothing) = return 0
pickupZ (Just x, Nothing) = return x
pickupZ (Nothing, Just x) = return x
pickupZ (Just x, Just y) = if x <= y then return x else mzero 

-- ---------------------------------------------------------------------------

gcd' :: [Integer] -> Integer
gcd' [] = 1
gcd' xs = foldl1' gcd xs

combine :: (a -> a -> a) -> Maybe a -> Maybe a -> Maybe a
combine _ Nothing y = y
combine _ x Nothing = x
combine f (Just x) (Just y) = Just (f x y)

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
