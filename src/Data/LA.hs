{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.LA
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
module Data.LA
  ( module Data.Linear

  -- * Expression of linear arithmetics
  , Expr

  -- ** Conversion
  , var
  , constant
  , terms
  , fromTerms
  , coeffMap
  , fromCoeffMap
  , unitVar
  , asConst

  -- ** Query
  , coeff
  , lookupCoeff
  , extract
  , extractMaybe  

  -- ** Operations
  , mapCoeff
  , mapCoeffWithVar
  , evalExpr
  , evalLinear
  , lift1
  , applySubst
  , applySubst1
  , showExpr

  -- * Atomic formula of linear arithmetics
  , Atom (..)
  , showAtom
  , evalAtom
  , solveFor

  -- * misc
  , BoundsEnv
  , computeInterval
  ) where

import Control.Monad
import Control.DeepSeq
import Data.List
import Data.Maybe
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import qualified Data.ArithRel as ArithRel
import Data.Linear
import Data.Interval
import Data.Var

-----------------------------------------------------------------------------

-- | Linear combination of variables and constants.
-- Non-negative keys are used for variables's coefficients.
-- key 'unitVar' is used for constants.
newtype Expr r
  = Expr
  { -- | a mapping from variables to coefficients
    coeffMap :: IM.IntMap r
  } deriving (Eq, Ord)

-- | Create a @Expr@ from a mapping from variables to coefficients.
fromCoeffMap :: (Num r, Eq r) => IM.IntMap r -> Expr r
fromCoeffMap m = normalizeExpr (Expr m)

-- | terms contained in the expression.
terms :: Expr r -> [(r,Var)]
terms (Expr m) = [(c,v) | (v,c) <- IM.toList m]

-- | Create a @Expr@ from a list of terms.
fromTerms :: (Num r, Eq r) => [(r,Var)] -> Expr r
fromTerms ts = fromCoeffMap $ IM.fromListWith (+) [(x,c) | (c,x) <- ts]

instance Variables (Expr r) where
  vars (Expr m) = IS.delete unitVar (IM.keysSet m)

instance Show r => Show (Expr r) where
  showsPrec d m  = showParen (d > 10) $
    showString "fromTerms " . shows (terms m)

instance (Num r, Eq r, Read r) => Read (Expr r) where
  readsPrec p = readParen (p > 10) $ \ r -> do
    ("fromTerms",s) <- lex r
    (xs,t) <- reads s
    return (fromTerms xs, t)

instance NFData r => NFData (Expr r) where
  rnf (Expr m) = rnf m

-- | Special variable that should always be evaluated to 1.
unitVar :: Var
unitVar = -1

asConst :: Num r => Expr r -> Maybe r
asConst (Expr m) =
  case IM.toList m of
    [] -> Just 0
    [(v,x)] | v==unitVar -> Just x
    _ -> Nothing

normalizeExpr :: (Num r, Eq r) => Expr r -> Expr r
normalizeExpr (Expr t) = Expr $ IM.filter (0/=) t

-- | variable
var :: Num r => Var -> Expr r
var v = Expr $ IM.singleton v 1

-- | constant
constant :: (Num r, Eq r) => r -> Expr r
constant c = normalizeExpr $ Expr $ IM.singleton unitVar c

-- | map coefficients.
mapCoeff :: (Num b, Eq b) => (a -> b) -> Expr a -> Expr b
mapCoeff f (Expr t) = Expr $ IM.mapMaybe g t
  where
    g c = if c' == 0 then Nothing else Just c'
      where c' = f c

-- | map coefficients.
mapCoeffWithVar :: (Num b, Eq b) => (a -> Var -> b) -> Expr a -> Expr b
mapCoeffWithVar f (Expr t) = Expr $ IM.mapMaybeWithKey g t
  where
    g v c = if c' == 0 then Nothing else Just c'
      where c' = f c v

instance (Num r, Eq r) => Module r (Expr r) where
  Expr t .+. e2 | IM.null t = e2
  e1 .+. Expr t | IM.null t = e1
  e1 .+. e2 = normalizeExpr $ plus e1 e2
  1 .*. e = e
  0 .*. e = lzero
  c .*. e = mapCoeff (c*) e
  lzero = Expr $ IM.empty

instance (Fractional r, Eq r) => Linear r (Expr r)

plus :: Num r => Expr r -> Expr r -> Expr r
plus (Expr t1) (Expr t2) = Expr $ IM.unionWith (+) t1 t2

-- | evaluate the expression under the model.
evalExpr :: Num r => Model r -> Expr r -> r
evalExpr m (Expr t) = sum [(m' IM.! v) * c | (v,c) <- IM.toList t]
  where m' = IM.insert unitVar 1 m

-- | evaluate the expression under the model.
evalLinear :: Linear r a => Model a -> a -> Expr r -> a
evalLinear m u (Expr t) = lsum [c .*. (m' IM.! v) | (v,c) <- IM.toList t]
  where m' = IM.insert unitVar u m

lift1 :: Linear r x => x -> (Var -> x) -> Expr r -> x
lift1 unit f (Expr t) = lsum [c .*. (g v) | (v,c) <- IM.toList t]
  where
    g v
      | v==unitVar = unit
      | otherwise   = f v

applySubst :: (Num r, Eq r) => VarMap (Expr r) -> Expr r -> Expr r
applySubst s (Expr m) = lsum (map f (IM.toList m))
  where
    f (v,c) = c .*. (
      case IM.lookup v s of
        Just tm -> tm
        Nothing -> var v)

-- | applySubst1 x e e1 == e1[e/x]
applySubst1 :: (Num r, Eq r) => Var -> Expr r -> Expr r -> Expr r
applySubst1 x e e1 =
  case extractMaybe x e1 of
    Nothing -> e1
    Just (c,e2) -> c .*. e .+. e2

-- | lookup a coefficient of the variable.
-- @
--   coeff v e == fst (extract v e)
-- @
coeff :: Num r => Var -> Expr r -> r
coeff v (Expr m) = IM.findWithDefault 0 v m

-- | lookup a coefficient of the variable.
-- It returns @Nothing@ if the expression does not contain @v@.
-- @
--   lookupCoeff v e == fmap fst (extractMaybe v e)
-- @
lookupCoeff :: Num r => Var -> Expr r -> Maybe r
lookupCoeff v (Expr m) = IM.lookup v m  

-- | @extract v e@ returns @(c, e')@ such that @e == c .*. v .+. e'@
extract :: Num r => Var -> Expr r -> (r, Expr r)
extract v (Expr m) = (IM.findWithDefault 0 v m, Expr (IM.delete v m))
{-
-- Alternative implementation which may be faster but allocte more memory
extract v (Expr m) = 
  case IM.updateLookupWithKey (\_ _ -> Nothing) v m of
    (Nothing, _) -> (0, Expr m)
    (Just c, m2) -> (c, Expr m2)
-}

-- | @extractMaybe v e@ returns @Just (c, e')@ such that @e == c .*. v .+. e'@
-- if @e@ contains v, and returns @Nothing@ otherwise.
extractMaybe :: Num r => Var -> Expr r -> Maybe (r, Expr r)
extractMaybe v (Expr m) =
  case IM.lookup v m of
    Nothing -> Nothing
    Just c -> Just (c, Expr (IM.delete v m))
{-
-- Alternative implementation which may be faster but allocte more memory
extractMaybe v (Expr m) =
  case IM.updateLookupWithKey (\_ _ -> Nothing) v m of
    (Nothing, _) -> Nothing
    (Just c, m2) -> Just (c, Expr m2)
-}

showExpr :: (Num r, Eq r, Show r) => Expr r -> String
showExpr = showExprWith f
  where
    f x = "x" ++ show x

showExprWith :: (Num r, Show r, Eq r) => (Var -> String) -> Expr r -> String
showExprWith env (Expr m) = foldr (.) id xs ""
  where
    xs = intersperse (showString " + ") ts
    ts = [if c==1
            then showString (env x)
            else showsPrec 8 c . showString "*" . showString (env x)
          | (x,c) <- IM.toList m, x /= unitVar] ++
         [showsPrec 7 c | c <- maybeToList (IM.lookup unitVar m)]

-----------------------------------------------------------------------------

-- | Atomic Formula of Linear Arithmetics
type Atom r = ArithRel.Rel (Expr r)

showAtom :: (Num r, Eq r, Show r) => Atom r -> String
showAtom (ArithRel.Rel lhs op rhs) = showExpr lhs ++ ArithRel.showOp op ++ showExpr rhs

-- | evaluate the formula under the model.
evalAtom :: (Num r, Ord r) => Model r -> Atom r -> Bool
evalAtom m (ArithRel.Rel lhs op rhs) = ArithRel.evalOp op (evalExpr m lhs) (evalExpr m rhs)

-- | Solve linear (in)equation for the given variable.
--
-- @solveFor a v@ returns @Just (op, e)@ such that @Atom v op e@
-- is equivalent to @a@.
solveFor :: (Real r, Fractional r) => Atom r -> Var -> Maybe (ArithRel.RelOp, Expr r)
solveFor (ArithRel.Rel lhs op rhs) v = do
  (c,e) <- extractMaybe v (lhs .-. rhs)
  return ( if c < 0 then ArithRel.flipOp op else op
         , (1/c) .*. lnegate e
         )

-----------------------------------------------------------------------------

type BoundsEnv r = VarMap (Interval r)

-- | compute bounds for a @Expr@ with respect to @BoundsEnv@.
computeInterval :: (Real r, Fractional r) => BoundsEnv r -> Expr r -> Interval r
computeInterval b = evalExpr b . mapCoeff singleton

-----------------------------------------------------------------------------
