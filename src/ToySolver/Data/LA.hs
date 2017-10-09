{-# LANGUAGE TypeFamilies, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Data.LA
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (TypeFamilies, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses)
--
-- Some definition for Theory of Linear Arithmetics.
-- 
-----------------------------------------------------------------------------
module ToySolver.Data.LA
  (
  -- * Expression of linear arithmetics
    Expr
  , Var

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
  , applySubstAtom
  , applySubst1Atom
  , solveFor
  , module ToySolver.Data.OrdRel

  -- * Evaluation of expression and atomic formula
  , Eval (..)

  -- * misc
  , BoundsEnv
  , computeInterval
  ) where

import Control.Monad
import Control.DeepSeq
import Data.List
import Data.Maybe
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntSet as IntSet
import Data.Interval
import Data.VectorSpace

import qualified ToySolver.Data.OrdRel as OrdRel
import ToySolver.Data.OrdRel
import ToySolver.Data.IntVar

-----------------------------------------------------------------------------

-- | Linear combination of variables and constants.
-- Non-negative keys are used for variables's coefficients.
-- key 'unitVar' is used for constants.
newtype Expr r
  = Expr
  { -- | a mapping from variables to coefficients
    coeffMap :: IntMap r
  } deriving (Eq, Ord)

-- | Create a @Expr@ from a mapping from variables to coefficients.
fromCoeffMap :: (Num r, Eq r) => IntMap r -> Expr r
fromCoeffMap m = normalizeExpr (Expr m)

-- | terms contained in the expression.
terms :: Expr r -> [(r,Var)]
terms (Expr m) = [(c,v) | (v,c) <- IntMap.toList m]

-- | Create a @Expr@ from a list of terms.
fromTerms :: (Num r, Eq r) => [(r,Var)] -> Expr r
fromTerms ts = fromCoeffMap $ IntMap.fromListWith (+) [(x,c) | (c,x) <- ts]

instance Variables (Expr r) where
  vars (Expr m) = IntSet.delete unitVar (IntMap.keysSet m)

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
  case IntMap.toList m of
    [] -> Just 0
    [(v,x)] | v==unitVar -> Just x
    _ -> Nothing

normalizeExpr :: (Num r, Eq r) => Expr r -> Expr r
normalizeExpr (Expr t) = Expr $ IntMap.filter (0/=) t

-- | variable
var :: Num r => Var -> Expr r
var v = Expr $ IntMap.singleton v 1

-- | constant
constant :: (Num r, Eq r) => r -> Expr r
constant c = normalizeExpr $ Expr $ IntMap.singleton unitVar c

-- | map coefficients.
mapCoeff :: (Num b, Eq b) => (a -> b) -> Expr a -> Expr b
mapCoeff f (Expr t) = Expr $ IntMap.mapMaybe g t
  where
    g c = if c' == 0 then Nothing else Just c'
      where c' = f c

-- | map coefficients.
mapCoeffWithVar :: (Num b, Eq b) => (a -> Var -> b) -> Expr a -> Expr b
mapCoeffWithVar f (Expr t) = Expr $ IntMap.mapMaybeWithKey g t
  where
    g v c = if c' == 0 then Nothing else Just c'
      where c' = f c v

instance (Num r, Eq r) => AdditiveGroup (Expr r) where
  Expr t ^+^ e2 | IntMap.null t = e2
  e1 ^+^ Expr t | IntMap.null t = e1
  e1 ^+^ e2 = normalizeExpr $ plus e1 e2
  zeroV = Expr $ IntMap.empty
  negateV = ((-1) *^)

instance (Num r, Eq r) => VectorSpace (Expr r) where
  type Scalar (Expr r) = r
  1 *^ e = e
  0 *^ e = zeroV
  c *^ e = mapCoeff (c*) e

plus :: Num r => Expr r -> Expr r -> Expr r
plus (Expr t1) (Expr t2) = Expr $ IntMap.unionWith (+) t1 t2

instance Num r => Eval (Model r) (Expr r) r where
  eval m (Expr t) = sum [(m' IntMap.! v) * c | (v,c) <- IntMap.toList t]
    where m' = IntMap.insert unitVar 1 m

{-# DEPRECATED evalExpr "Use Eval class instead" #-}
-- | evaluate the expression under the model.
evalExpr :: Num r => Model r -> Expr r -> r
evalExpr = eval

-- | evaluate the expression under the model.
evalLinear :: VectorSpace a => Model a -> a -> Expr (Scalar a) -> a
evalLinear m u (Expr t) = sumV [c *^ (m' IntMap.! v) | (v,c) <- IntMap.toList t]
  where m' = IntMap.insert unitVar u m

lift1 :: VectorSpace x => x -> (Var -> x) -> Expr (Scalar x) -> x
lift1 unit f (Expr t) = sumV [c *^ (g v) | (v,c) <- IntMap.toList t]
  where
    g v
      | v==unitVar = unit
      | otherwise   = f v

applySubst :: (Num r, Eq r) => VarMap (Expr r) -> Expr r -> Expr r
applySubst s (Expr m) = sumV (map f (IntMap.toList m))
  where
    f (v,c) = c *^ (
      case IntMap.lookup v s of
        Just tm -> tm
        Nothing -> var v)

-- | applySubst1 x e e1 == e1[e/x]
applySubst1 :: (Num r, Eq r) => Var -> Expr r -> Expr r -> Expr r
applySubst1 x e e1 =
  case extractMaybe x e1 of
    Nothing -> e1
    Just (c,e2) -> c *^ e ^+^ e2

-- | lookup a coefficient of the variable.
-- @
--   coeff v e == fst (extract v e)
-- @
coeff :: Num r => Var -> Expr r -> r
coeff v (Expr m) = IntMap.findWithDefault 0 v m

-- | lookup a coefficient of the variable.
-- It returns @Nothing@ if the expression does not contain @v@.
-- @
--   lookupCoeff v e == fmap fst (extractMaybe v e)
-- @
lookupCoeff :: Num r => Var -> Expr r -> Maybe r
lookupCoeff v (Expr m) = IntMap.lookup v m  

-- | @extract v e@ returns @(c, e')@ such that @e == c *^ v ^+^ e'@
extract :: Num r => Var -> Expr r -> (r, Expr r)
extract v (Expr m) = (IntMap.findWithDefault 0 v m, Expr (IntMap.delete v m))
{-
-- Alternative implementation which may be faster but allocte more memory
extract v (Expr m) = 
  case IntMap.updateLookupWithKey (\_ _ -> Nothing) v m of
    (Nothing, _) -> (0, Expr m)
    (Just c, m2) -> (c, Expr m2)
-}

-- | @extractMaybe v e@ returns @Just (c, e')@ such that @e == c *^ v ^+^ e'@
-- if @e@ contains v, and returns @Nothing@ otherwise.
extractMaybe :: Num r => Var -> Expr r -> Maybe (r, Expr r)
extractMaybe v (Expr m) =
  case IntMap.lookup v m of
    Nothing -> Nothing
    Just c -> Just (c, Expr (IntMap.delete v m))
{-
-- Alternative implementation which may be faster but allocte more memory
extractMaybe v (Expr m) =
  case IntMap.updateLookupWithKey (\_ _ -> Nothing) v m of
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
          | (x,c) <- IntMap.toList m, x /= unitVar] ++
         [showsPrec 7 c | c <- maybeToList (IntMap.lookup unitVar m)]

-----------------------------------------------------------------------------

-- | Atomic Formula of Linear Arithmetics
type Atom r = OrdRel (Expr r)

showAtom :: (Num r, Eq r, Show r) => Atom r -> String
showAtom (OrdRel lhs op rhs) = showExpr lhs ++ showOp op ++ showExpr rhs

{-# DEPRECATED evalAtom "Use Eval class instead" #-}
-- | evaluate the formula under the model.
evalAtom :: (Num r, Ord r) => Model r -> Atom r -> Bool
evalAtom = eval

applySubstAtom :: (Num r, Eq r) => VarMap (Expr r) -> Atom r -> Atom r
applySubstAtom s (OrdRel lhs op rhs) = OrdRel (applySubst s lhs) op (applySubst s rhs)

-- | applySubst1 x e phi == phi[e/x]
applySubst1Atom :: (Num r, Eq r) => Var -> Expr r -> Atom r -> Atom r
applySubst1Atom x e (OrdRel lhs op rhs) = OrdRel (applySubst1 x e lhs) op (applySubst1 x e rhs)

-- | Solve linear (in)equation for the given variable.
--
-- @solveFor a v@ returns @Just (op, e)@ such that @Atom v op e@
-- is equivalent to @a@.
solveFor :: (Real r, Fractional r) => Atom r -> Var -> Maybe (RelOp, Expr r)
solveFor (OrdRel lhs op rhs) v = do
  (c,e) <- extractMaybe v (lhs ^-^ rhs)
  return ( if c < 0 then flipOp op else op
         , (1/c) *^ negateV e
         )

-----------------------------------------------------------------------------

type BoundsEnv r = VarMap (Interval r)

-- | compute bounds for a @Expr@ with respect to @BoundsEnv@.
computeInterval :: (Real r, Fractional r) => BoundsEnv r -> Expr r -> Interval r
computeInterval b = evalExpr b . mapCoeff singleton

-----------------------------------------------------------------------------
