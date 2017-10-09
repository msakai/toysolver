{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Arith.Cooper.Base
-- Copyright   :  (c) Masahiro Sakai 2011-2014
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (MultiParamTypeClasses, FlexibleInstances)
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
module ToySolver.Arith.Cooper.Base
    (
    -- * Language of presburger arithmetics
      ExprZ
    , Lit (..)
    , evalLit
    , QFFormula
    , fromLAAtom
    , (.|.)
    , evalQFFormula
    , Model
    , Eval (..)

    -- * Projection
    , project
    , projectN
    , projectCases
    , projectCasesN

    -- * Constraint solving
    , solve
    , solveQFFormula
    , solveQFLIRAConj
    ) where

import Control.Monad
import qualified Data.Foldable as Foldable
import Data.List
import Data.Maybe
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Data.Monoid
import Data.Ratio
import Data.Set (Set)
import qualified Data.Set as Set
import Data.VectorSpace hiding (project)

import ToySolver.Data.OrdRel
import ToySolver.Data.Boolean
import ToySolver.Data.BoolExpr (BoolExpr (..))
import qualified ToySolver.Data.BoolExpr as BoolExpr
import qualified ToySolver.Data.LA as LA
import ToySolver.Data.IntVar
import qualified ToySolver.Arith.FourierMotzkin as FM

-- ---------------------------------------------------------------------------

-- | Linear arithmetic expression over integers.
type ExprZ = LA.Expr Integer

fromLAAtom :: LA.Atom Rational -> QFFormula
fromLAAtom (OrdRel a op b) = ordRel op a' b'
  where
    (e1,c1) = toRat a
    (e2,c2) = toRat b
    a' = c2 *^ e1
    b' = c1 *^ e2

-- | (t,c) represents t/c, and c must be >0.
type Rat = (ExprZ, Integer)

toRat :: LA.Expr Rational -> Rat
toRat e = seq m $ (LA.mapCoeff f e, m)
  where
    f x = numerator (fromInteger m * x)
    m = foldl' lcm 1 [denominator c | (c,_) <- LA.terms e]

leZ, ltZ, geZ, gtZ :: ExprZ -> ExprZ -> Lit
leZ e1 e2 = e1 `ltZ` (e2 ^+^ LA.constant 1)
ltZ e1 e2 = IsPos $ (e2 ^-^ e1)
geZ = flip leZ
gtZ = flip ltZ

eqZ :: ExprZ -> ExprZ -> QFFormula
eqZ e1 e2 = Atom (e1 `leZ` e2) .&&. Atom (e1 `geZ` e2)

-- | Literals of Presburger arithmetic.
data Lit
    = IsPos ExprZ
    -- ^ @IsPos e@ means @e > 0@
    | Divisible Bool Integer ExprZ
    -- ^
    -- * @Divisible True d e@ means @e@ can be divided by @d@ (i.e. @d | e@)
    -- * @Divisible False d e@ means @e@ can not be divided by @d@ (i.e. @¬(d | e)@)
    deriving (Show, Eq, Ord)

instance Variables Lit where
  vars (IsPos t) = vars t
  vars (Divisible _ _ t) = vars t

instance Complement Lit where
  notB (IsPos e) = e `leZ` LA.constant 0
  notB (Divisible b c e) = Divisible (not b) c e

-- | Quantifier-free formula of Presburger arithmetic.
type QFFormula = BoolExpr Lit

instance IsEqRel (LA.Expr Integer) QFFormula where
  a .==. b = eqZ a b
  a ./=. b = notB $ eqZ a b
  
instance IsOrdRel (LA.Expr Integer) QFFormula where
  ordRel op lhs rhs =
    case op of
      Le  -> Atom $ leZ lhs rhs
      Ge  -> Atom $ geZ lhs rhs
      Lt  -> Atom $ ltZ lhs rhs
      Gt  -> Atom $ gtZ lhs rhs
      Eql -> lhs .==. rhs
      NEq -> lhs ./=. rhs

-- | @d | e@ means @e@ can be divided by @d@.
(.|.) :: Integer -> ExprZ -> QFFormula
n .|. e = Atom $ Divisible True n e

subst1 :: Var -> ExprZ -> QFFormula -> QFFormula
subst1 x e = fmap f
  where
    f (Divisible b c e1) = Divisible b c $ LA.applySubst1 x e e1
    f (IsPos e1) = IsPos $ LA.applySubst1 x e e1

simplify :: QFFormula -> QFFormula
simplify = BoolExpr.simplify . BoolExpr.fold simplifyLit

simplifyLit :: Lit -> QFFormula
simplifyLit (IsPos e) =
  case LA.asConst e of
    Just c -> if c > 0 then true else false
    Nothing ->
      -- e > 0  <=>  e - 1 >= 0
      -- <=>  LA.mapCoeff (`div` d) (e - 1) >= 0
      -- <=>  LA.mapCoeff (`div` d) (e - 1) + 1 > 0
      Atom $ IsPos $ LA.mapCoeff (`div` d) e1 ^+^ LA.constant 1
  where
    e1 = e ^-^ LA.constant 1
    d  = if null cs then 1 else abs $ foldl1' gcd cs
    cs = [c | (c,x) <- LA.terms e1, x /= LA.unitVar]
simplifyLit lit@(Divisible b c e)
  | LA.coeff LA.unitVar e2 `mod` d /= 0 = if b then false else true
  | c' == 1   = if b then true else false
  | d  == 1   = Atom lit
  | otherwise = Atom $ Divisible b c' e'
  where
    e2 = LA.mapCoeff (`mod` c) e
    d  = abs $ foldl' gcd c [c2 | (c2,x) <- LA.terms e2, x /= LA.unitVar]
    c' = c `checkedDiv` d
    e' = LA.mapCoeff (`checkedDiv` d) e2

{-# DEPRECATED evalQFFormula "Use Eval class instead" #-}
-- | @'evalQFFormula' M φ@ returns whether @M ⊧_LIA φ@ or not.
evalQFFormula :: Model Integer -> QFFormula -> Bool
evalQFFormula = eval

{-# DEPRECATED evalLit "Use Eval class instead" #-}
evalLit :: Model Integer -> Lit -> Bool
evalLit = eval

instance Eval (Model Integer) Lit Bool where
  eval m (IsPos e) = LA.eval m e > 0
  eval m (Divisible True n e)  = LA.eval m e `mod` n == 0
  eval m (Divisible False n e) = LA.eval m e `mod` n /= 0

-- ---------------------------------------------------------------------------

data Witness = WCase1 Integer ExprZ | WCase2 Integer Integer Integer (Set ExprZ)
  deriving (Show)

instance Eval (Model Integer) Witness Integer where
  eval model (WCase1 c e) = LA.eval model e `checkedDiv` c
  eval model (WCase2 c j delta us)
    | Set.null us' = j `checkedDiv` c
    | otherwise = (j + (((u - delta - 1) `div` delta) * delta)) `checkedDiv` c
    where
      us' = Set.map (LA.eval model) us
      u = Set.findMin us'

-- ---------------------------------------------------------------------------

{-| @'project' x φ@ returns @(ψ, lift)@ such that:

* @⊢_LIA ∀y1, …, yn. (∃x. φ) ↔ ψ@ where @{y1, …, yn} = FV(φ) \\ {x}@, and

* if @M ⊧_LIA ψ@ then @lift M ⊧_LIA φ@.
-}
project :: Var -> QFFormula -> (QFFormula, Model Integer -> Model Integer)
project x formula = (formula', mt)
  where
    xs = projectCases x formula
    formula' = orB' [phi | (phi,_) <- xs]
    mt m = head $ do
      (phi, mt') <- xs
      guard $ eval m phi
      return $ mt' m
    orB' = orB . concatMap f
      where
        f (Or xs) = concatMap f xs
        f x = [x]

{-| @'projectN' {x1,…,xm} φ@ returns @(ψ, lift)@ such that:

* @⊢_LIA ∀y1, …, yn. (∃x1, …, xm. φ) ↔ ψ@ where @{y1, …, yn} = FV(φ) \\ {x1,…,xm}@, and

* if @M ⊧_LIA ψ@ then @lift M ⊧_LIA φ@.
-}
projectN :: VarSet -> QFFormula -> (QFFormula, Model Integer -> Model Integer)
projectN vs2 = f (IS.toList vs2)
  where
    f :: [Var] -> QFFormula -> (QFFormula, Model Integer -> Model Integer)
    f [] formula     = (formula, id)
    f (v:vs) formula = (formula3, mt1 . mt2)
      where
        (formula2, mt1) = project v formula
        (formula3, mt2) = f vs formula2

{-| @'projectCases' x φ@ returns @[(ψ_1, lift_1), …, (ψ_m, lift_m)]@ such that:

* @⊢_LIA ∀y1, …, yn. (∃x. φ) ↔ (ψ_1 ∨ … ∨ φ_m)@ where @{y1, …, yn} = FV(φ) \\ {x}@, and

* if @M ⊧_LIA ψ_i@ then @lift_i M ⊧_LIA φ@.
-}
projectCases :: Var -> QFFormula -> [(QFFormula, Model Integer -> Model Integer)]
projectCases x formula = do
  (phi, wit) <- projectCases' x formula
  return (phi, \m -> IM.insert x (eval m wit) m)

projectCases' :: Var -> QFFormula -> [(QFFormula, Witness)]
projectCases' x formula = [(phi', w) | (phi,w) <- case1 ++ case2, let phi' = simplify phi, phi' /= false]
  where
    -- eliminate Not, Imply and Equiv.
    formula0 :: QFFormula
    formula0 = pos formula
      where
        pos (Atom a) = Atom a
        pos (And xs) = And (map pos xs)
        pos (Or xs) = Or (map pos xs)
        pos (Not x) = neg x
        pos (Imply x y) = neg x .||. pos y
        pos (Equiv x y) = pos ((x .=>. y) .&&. (y .=>. x))
        pos (ITE c t e) = pos ((c .=>. t) .&&. (Not c .=>. e))

        neg (Atom a) = Atom (notB a)
        neg (And xs) = Or (map neg xs)
        neg (Or xs) = And (map neg xs)
        neg (Not x) = pos x
        neg (Imply x y) = pos x .&&. neg y
        neg (Equiv x y) = neg ((x .=>. y) .&&. (y .=>. x))
        neg (ITE c t e) = neg ((c .=>. t) .&&. (Not c .=>. e))

    -- xの係数の最小公倍数
    c :: Integer
    c = getLCM $ Foldable.foldMap f formula0
      where
         f (IsPos e) = LCM $ fromMaybe 1 (LA.lookupCoeff x e)
         f (Divisible _ _ e) = LCM $ fromMaybe 1 (LA.lookupCoeff x e)

    -- 式をスケールしてxの係数の絶対値をcへと変換し、その後cxをxで置き換え、
    -- xがcで割り切れるという制約を追加した論理式
    formula1 :: QFFormula
    formula1 = simplify $ fmap f formula0 .&&. (c .|. LA.var x)
      where
        f lit@(IsPos e) =
          case LA.lookupCoeff x e of
            Nothing -> lit
            Just a ->
              let s = abs (c `checkedDiv` a)
              in IsPos $ g s e
        f lit@(Divisible b d e) =
          case LA.lookupCoeff x e of
            Nothing -> lit
            Just a ->
              let s = abs (c `checkedDiv` a)
              in Divisible b (s*d) $ g s e

        g :: Integer -> ExprZ -> ExprZ
        g s = LA.mapCoeffWithVar (\c' x' -> if x==x' then signum c' else s*c')

    -- d|x+t という形の論理式の d の最小公倍数
    delta :: Integer
    delta = getLCM $ Foldable.foldMap f formula1
      where
        f (Divisible _ d _) = LCM d
        f (IsPos _) = LCM 1

    -- ts = {t | t < x は formula1 に現れる原子論理式}
    ts :: Set ExprZ
    ts = Foldable.foldMap f formula1
      where
        f (Divisible _ _ _) = Set.empty
        f (IsPos e) =
          case LA.extractMaybe x e of
            Nothing -> Set.empty
            Just (1, e') -> Set.singleton (negateV e') -- IsPos e <=> (x + e' > 0) <=> (-e' < x)
            Just (-1, _) -> Set.empty -- IsPos e <=> (-x + e' > 0) <=> (x < e')
            _ -> error "should not happen"

    -- formula1を真にする最小のxが存在する場合
    case1 :: [(QFFormula, Witness)]
    case1 = [ (subst1 x e formula1, WCase1 c e)
            | j <- [1..delta], t <- Set.toList ts, let e = t ^+^ LA.constant j ]

    -- formula1のなかの x < t を真に t < x を偽に置き換えた論理式
    formula2 :: QFFormula
    formula2 = simplify $ BoolExpr.fold f formula1
      where        
        f lit@(IsPos e) =
          case LA.lookupCoeff x e of
            Nothing -> Atom lit
            Just 1    -> false -- IsPos e <=> ( x + e' > 0) <=> -e' < x
            Just (-1) -> true  -- IsPos e <=> (-x + e' > 0) <=>  x  < e'
            _ -> error "should not happen"
        f lit@(Divisible _ _ _) = Atom lit

    -- us = {u | x < u は formula1 に現れる原子論理式}
    us :: Set ExprZ
    us = Foldable.foldMap f formula1
      where
        f (IsPos e) =
          case LA.extractMaybe x e of
            Nothing -> Set.empty
            Just (1, _)   -> Set.empty -- IsPos e <=> (x + e' > 0) <=> -e' < x
            Just (-1, e') -> Set.singleton e' -- IsPos e <=> (-x + e' > 0) <=>  x  < e'
            _ -> error "should not happen"
        f (Divisible _ _ _) = Set.empty

    -- formula1を真にする最小のxが存在しない場合
    case2 :: [(QFFormula, Witness)]
    case2 = [(subst1 x (LA.constant j) formula2, WCase2 c j delta us) | j <- [1..delta]]

{-| @'projectCasesN' {x1,…,xm} φ@ returns @[(ψ_1, lift_1), …, (ψ_n, lift_n)]@ such that:

* @⊢_LIA ∀y1, …, yp. (∃x. φ) ↔ (ψ_1 ∨ … ∨ φ_n)@ where @{y1, …, yp} = FV(φ) \\ {x1,…,xm}@, and

* if @M ⊧_LIA ψ_i@ then @lift_i M ⊧_LIA φ@.
-}
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

newtype LCM a = LCM{ getLCM :: a }

instance Integral a => Monoid (LCM a) where
  mempty = LCM 1
  LCM a `mappend` LCM b = LCM $ lcm a b

checkedDiv :: Integer -> Integer -> Integer
checkedDiv a b =
  case a `divMod` b of
    (q,0) -> q
    _ -> error "ToySolver.Cooper.checkedDiv: should not happen"

-- ---------------------------------------------------------------------------

-- | @'solveQFFormula' {x1,…,xn} φ@ returns @Just M@ that @M ⊧_LIA φ@ when
-- such @M@ exists, returns @Nothing@ otherwise.
--
-- @FV(φ)@ must be a subset of @{x1,…,xn}@.
-- 
solveQFFormula :: VarSet -> QFFormula -> Maybe (Model Integer)
solveQFFormula vs formula = listToMaybe $ do
  (formula2, mt) <- projectCasesN vs formula
  let m :: Model Integer
      m = IM.empty
  guard $ eval m formula2
  return $ mt m

-- | @'solve' {x1,…,xn} φ@ returns @Just M@ that @M ⊧_LIA φ@ when
-- such @M@ exists, returns @Nothing@ otherwise.
--
-- @FV(φ)@ must be a subset of @{x1,…,xn}@.
-- 
solve :: VarSet -> [LA.Atom Rational] -> Maybe (Model Integer)
solve vs cs = solveQFFormula vs $ andB $ map fromLAAtom cs

-- | @'solveQFLIRAConj' {x1,…,xn} φ I@ returns @Just M@ that @M ⊧_LIRA φ@ when
-- such @M@ exists, returns @Nothing@ otherwise.
--
-- * @FV(φ)@ must be a subset of @{x1,…,xn}@.
--
-- * @I@ is a set of integer variables and must be a subset of @{x1,…,xn}@.
-- 
solveQFLIRAConj :: VarSet -> [LA.Atom Rational] -> VarSet -> Maybe (Model Rational)
solveQFLIRAConj vs cs ivs = listToMaybe $ do
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
∃ x. x < y+y ∧ z<x ∧ 3|x
⇔
(2y>z+1 ∧ 3|z+1) ∨ (2y>z+2 ∧ 3|z+2) ∨ (2y>z+3 ∧ 3|z+3)
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
