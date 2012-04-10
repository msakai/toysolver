{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  LA
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (MultiParamTypeClasses, FlexibleInstances)
--
-- Some definition for Theory of Linear Arithmetics.
-- 
-----------------------------------------------------------------------------
module LA
  ( module Linear

  -- * Expression of linear arithmetics
  , Expr
  , terms
  , fromTerms
  , coeffMap
  , fromCoeffMap
  , constVar
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
  , extract
  , extract'
  , showExpr

  -- * Atomic formula of linear arithmetics
  , Atom (..)
  , showAtom
  , solveFor

  -- * misc
  , BoundsEnv
  , computeInterval
  , compileExpr
  , compileAtom
  ) where

import Control.Monad
import Data.List
import Data.Maybe
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import qualified Expr
import Expr (Var, VarMap, VarSet, Variables, Model)
import qualified Formula
import Linear
import Interval

-----------------------------------------------------------------------------

-- | Linear combination of variables and constants.
-- Non-negative keys are used for variables's coefficients.
-- key 'constVar' is used for constants.
newtype Expr r
  = Expr
  { coeffMap :: IM.IntMap r
  } deriving (Eq, Ord)

-- | Create a @Expr@ from a mapping from variables to coefficients.
fromCoeffMap :: Num r => IM.IntMap r -> Expr r
fromCoeffMap m = normalizeExpr (Expr m)

-- | terms contained in the expression.
terms :: Expr r -> [(r,Var)]
terms (Expr m) = [(c,v) | (v,c) <- IM.toList m]

-- | Create a @Expr@ from a list of terms.
fromTerms :: Num r => [(r,Var)] -> Expr r
fromTerms ts = fromCoeffMap $ IM.fromListWith (+) [(x,c) | (c,x) <- ts]

instance Variables (Expr r) where
  vars (Expr m) = IS.delete constVar (IM.keysSet m)

instance Show r => Show (Expr r) where
  showsPrec d m  = showParen (d > 10) $
    showString "fromTerms " . shows (terms m)

instance (Num r, Read r) => Read (Expr r) where
  readsPrec p = readParen (p > 10) $ \ r -> do
    ("fromTerms",s) <- lex r
    (xs,t) <- reads s
    return (fromTerms xs, t)

-- | Special variable that should always be evaluated to 1.
constVar :: Var
constVar = -1

asConst :: Num r => Expr r -> Maybe r
asConst (Expr m) =
  case IM.toList m of
    [] -> Just 0
    [(v,x)] | v==constVar -> Just x
    _ -> Nothing

normalizeExpr :: Num r => Expr r -> Expr r
normalizeExpr (Expr t) = Expr $ IM.filter (0/=) t

-- | variable
varExpr :: Num r => Var -> Expr r
varExpr v = Expr $ IM.singleton v 1

-- | constant
constExpr :: Num r => r -> Expr r
constExpr c = normalizeExpr $ Expr $ IM.singleton constVar c

-- | map coefficients.
mapCoeff :: Num b => (a -> b) -> Expr a -> Expr b
mapCoeff f (Expr t) = Expr $ IM.mapMaybe g t
  where
    g c = if c' == 0 then Nothing else Just c'
      where c' = f c

-- | map coefficients.
mapCoeffWithVar :: Num b => (a -> Var -> b) -> Expr a -> Expr b
mapCoeffWithVar f (Expr t) = Expr $ IM.mapMaybeWithKey g t
  where
    g v c = if c' == 0 then Nothing else Just c'
      where c' = f c v

instance Num r => Linear r (Expr r) where
  e1 .+. e2 = normalizeExpr $ plus e1 e2
  c .*. e = mapCoeff (c*) e
  lzero = Expr $ IM.empty

plus :: Num r => Expr r -> Expr r -> Expr r
plus (Expr t1) (Expr t2) = Expr $ IM.unionWith (+) t1 t2

-- | evaluate the expression under the model.
evalExpr :: Num r => Model r -> Expr r -> r
evalExpr m (Expr t) = sum [(m' IM.! v) * c | (v,c) <- IM.toList t]
  where m' = IM.insert constVar 1 m

lift1 :: Linear r x => x -> (Var -> x) -> Expr r -> x
lift1 unit f (Expr t) = lsum [c .*. (g v) | (v,c) <- IM.toList t]
  where
    g v
      | v==constVar = unit
      | otherwise   = f v

applySubst :: Num r => VarMap (Expr r) -> Expr r -> Expr r
applySubst s (Expr m) = lsum (map f (IM.toList m))
  where
    f (v,c) = c .*. (
      case IM.lookup v s of
        Just tm -> tm
        Nothing -> varExpr v)

applySubst1 :: Num r => Var -> Expr r -> Expr r -> Expr r
applySubst1 x e e1 =
  case extract' x e1 of
    Nothing -> e1
    Just (c,e2) -> c .*. e .+. e2

-- | lookup a coefficient of the variable.
-- @
--   lookupCoeff v e == fst (extract v e)
-- @
lookupCoeff :: Num r => Var -> Expr r -> r
lookupCoeff v (Expr m) = IM.findWithDefault 0 v m

-- | lookup a coefficient of the variable.
-- It returns @Nothing@ if the expression does not contain @v@.
-- @
--   lookupCoeff' v e == fmap fst (extract' v e)
-- @
lookupCoeff' :: Num r => Var -> Expr r -> Maybe r
lookupCoeff' v (Expr m) = IM.lookup v m  

-- | @extract v e@ returns @(c, e')@ such that @e == c .*. v .+. e'@
extract :: Num r => Var -> Expr r -> (r, Expr r)
extract v (Expr m) = (IM.findWithDefault 0 v m, Expr (IM.delete v m))

-- | @extract' v e@ returns @Just (c, e')@ such that @e == c .*. v .+. e'@
-- if @e@ contains v, and returns @Nothing@ otherwise.
extract' :: Num r => Var -> Expr r -> Maybe (r, Expr r)
extract' v (Expr m) =
  case IM.lookup v m of
    Nothing -> Nothing
    Just c -> Just (c, Expr (IM.delete v m))

showExpr :: (Num r, Show r) => Expr r -> String
showExpr = showExprWith f
  where
    f x = "x" ++ show x

showExprWith :: (Num r, Show r) => (Var -> String) -> Expr r -> String
showExprWith env (Expr m) = foldr (.) id xs ""
  where
    xs = intersperse (showString " + ") ts
    ts = [if c==1
            then showString (env x)
            else showsPrec 8 c . showString "*" . showString (env x)
          | (x,c) <- IM.toList m, x /= constVar] ++
         [showsPrec 7 c | c <- maybeToList (IM.lookup constVar m)]

-----------------------------------------------------------------------------

-- | Atomic Formula of Linear Arithmetics
data Atom r = Atom (Expr r) Formula.RelOp (Expr r)
    deriving (Show, Eq, Ord)

instance Formula.Complement (Atom r) where
  notF (Atom  lhs op rhs) = Atom lhs (Formula.negOp op) rhs

instance Variables (Atom r) where
  vars (Atom a _ b) = Expr.vars a `IS.union` Expr.vars b

instance Formula.Rel (Expr r) (Atom r) where
  rel op a b = Atom a op b

showAtom :: (Num r, Show r) => Atom r -> String
showAtom (Atom lhs op rhs) = showExpr lhs ++ Formula.showOp op ++ showExpr rhs

-- | Solve linear (in)equation for the given variable.
--
-- @solveFor a v@ returns @Just (op, e)@ such that @Atom v op e@
-- is equivalent to @a@.
solveFor :: (Real r, Fractional r) => Atom r -> Var -> Maybe (Formula.RelOp, Expr r)
solveFor (Atom lhs op rhs) v = do
  (c,e) <- extract' v (lhs .-. rhs)
  return ( if c < 0 then Formula.flipOp op else op
         , (1/c) .*. lnegate e
         )

-----------------------------------------------------------------------------

type BoundsEnv r = Expr.VarMap (Interval r)

-- | compute bounds for a @Expr@ with respect to @BoundsEnv@.
computeInterval :: (Real r, Fractional r) => BoundsEnv r -> Expr r -> Interval r
computeInterval b = lift1 (singleton 1) (b IM.!)

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
