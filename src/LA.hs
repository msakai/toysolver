{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  LA
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
--
-- Some definition for Theory of Linear Arithmetics.
-- 
-----------------------------------------------------------------------------
module LA
  ( module Linear

  , Expr
  , terms
  , coeffMap
  , fromCoeffMap
  , constKey
  , asConst
  , varExpr
  , constExpr
  , mapCoeff
  , mapCoeffWithVar
  , evalExpr
  , lift1
  , applySubst
  , applySubst1
  , lookupCoeff
  , lookupCoeff'
  , pickupTerm
  , pickupTerm'

  , Atom (..)

  , Bounds
  , compileExpr
  , compileAtom
  ) where

import Control.Monad
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import qualified Expr
import Expr (Var, VarMap, VarSet, Variables, Model)
import qualified Formula
import Linear
import Interval

-----------------------------------------------------------------------------

-- Linear combination of variables and constants.
-- Non-negative keys are used for variables's coefficients.
-- key '-1' is used for constants.
newtype Expr r = Expr{ coeffMap :: IM.IntMap r } deriving (Eq, Ord, Show)

fromCoeffMap :: Num r => IM.IntMap r -> Expr r
fromCoeffMap m = normalizeExpr (Expr m)

terms :: Expr r -> [(r,Var)]
terms (Expr m) = [(c,v) | (v,c) <- IM.toList m]

instance Variables (Expr r) where
  vars (Expr m) = IS.delete constKey (IM.keysSet m)

constKey :: Int
constKey = -1

asConst :: Num r => Expr r -> Maybe r
asConst (Expr m) =
  case IM.toList m of
    [] -> Just 0
    [(v,x)] | v==constKey -> Just x
    _ -> Nothing

normalizeExpr :: Num r => Expr r -> Expr r
normalizeExpr (Expr t) = Expr $ IM.filter (0/=) t

varExpr :: Num r => Var -> Expr r
varExpr v = Expr $ IM.singleton v 1

constExpr :: Num r => r -> Expr r
constExpr c = normalizeExpr $ Expr $ IM.singleton constKey c

mapCoeff :: Num b => (a -> b) -> Expr a -> Expr b
mapCoeff f (Expr t) = normalizeExpr $ Expr $ IM.map f t

mapCoeffWithVar :: Num b => (a -> Var -> b) -> Expr a -> Expr b
mapCoeffWithVar f (Expr t) = normalizeExpr $ Expr $ IM.mapWithKey (flip f) t

instance Num r => Linear r (Expr r) where
  Expr t1 .+. Expr t2 = normalizeExpr $ Expr $ IM.unionWith (+) t1 t2
  c .*. (Expr t) = normalizeExpr $ Expr $ IM.map (c*) t
  lzero = Expr $ IM.empty

evalExpr :: Num r => Model r -> Expr r -> r
evalExpr m (Expr t) = sum [(m' IM.! v) * c | (v,c) <- IM.toList t]
  where m' = IM.insert constKey 1 m

lift1 :: Linear r x => x -> (Var -> x) -> Expr r -> x
lift1 unit f (Expr t) = lsum [c .*. (g v) | (v,c) <- IM.toList t]
  where
    g v
      | v==constKey = unit
      | otherwise   = f v

applySubst :: Num r => VarMap (Expr r) -> Expr r -> Expr r
applySubst s (Expr m) = lsum (map f (IM.toList m))
  where
    f (v,c) = c .*. (
      case IM.lookup v s of
        Just tm -> tm
        Nothing -> varExpr v)

applySubst1 :: Num r => Var -> Expr r -> Expr r -> Expr r
applySubst1 x e e1@(Expr m) = 
  case pickupTerm' x e1 of
    Nothing -> e1
    Just (c,e2) -> c .*. e .+. e2

lookupCoeff :: Num r => Var -> Expr r -> r
lookupCoeff v (Expr m) = IM.findWithDefault 0 v m

lookupCoeff' :: Num r => Var -> Expr r -> Maybe r
lookupCoeff' v (Expr m) = IM.lookup v m  

pickupTerm :: Num r => Var -> Expr r -> (r, Expr r)
pickupTerm v (Expr m) = (IM.findWithDefault 0 v m, Expr (IM.delete v m))

pickupTerm' :: Num r => Var -> Expr r -> Maybe (r, Expr r)
pickupTerm' v (Expr m) =
  case IM.lookup v m of
    Nothing -> Nothing
    Just c -> Just (c, Expr (IM.delete v m))

-----------------------------------------------------------------------------

-- | Atomic Formula
data Atom r = Atom (Expr r) Formula.RelOp (Expr r)
    deriving (Show, Eq, Ord)

instance Formula.Complement (Atom r) where
  notF (Atom  lhs op rhs) = Atom lhs (Formula.negOp op) rhs

instance Variables (Atom r) where
  vars (Atom a _ b) = Expr.vars a `IS.union` Expr.vars b

instance Formula.Rel (Expr r) (Atom r) where
  rel op a b = Atom a op b

type Bounds r = Expr.VarMap (Interval r)

-----------------------------------------------------------------------------

compileExpr :: (Real r, Fractional r) => Expr.Expr r -> Maybe (Expr r)
compileExpr (Expr.Const c) = return (constExpr c)
compileExpr (Expr.Var c) = return (varExpr c)
compileExpr (a Expr.:+: b) = liftM2 (.+.) (compileExpr a) (compileExpr b)
compileExpr (a Expr.:*: b) = do
  x <- compileExpr a
  y <- compileExpr b
  msum [ do{ c <- asConst x; return (c .*. y) }
       , do{ c <- asConst y; return (c .*. x) }
       ]
compileExpr (a Expr.:/: b) = do
  x <- compileExpr a
  c <- asConst =<< compileExpr b
  return $ (1/c) .*. x

compileAtom :: (Real r, Fractional r) => Formula.Atom r -> Maybe (Atom r)
compileAtom (Formula.Rel a op b) = do
  a' <- compileExpr a
  b' <- compileExpr b
  return $ Atom a' op b'

-----------------------------------------------------------------------------
