{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.LPSolver
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  non-portable (ScopedTypeVariables)
--
-- Naïve implementation of Simplex method
-- 
-- Reference:
--
-- * <http://www.math.cuhk.edu.hk/~wei/lpch3.pdf>
--
-----------------------------------------------------------------------------

module ToySolver.LPSolver
  (
  -- * Solver type
    Solver
  , emptySolver

  -- * LP monad
  , LP
  , getTableau
  , putTableau

  -- * Problem specification
  , newVar
  , addConstraint
  , addConstraintWithArtificialVariable
  , tableau
  , define

  -- * Solving
  , phaseI
  , simplex
  , dualSimplex
  , OptResult (..)
  , twoPhaseSimplex
  , primalDualSimplex

  -- * Extract results
  , getModel

  -- * Utilities
  , collectNonnegVars
  ) where

import Control.Exception (assert)
import Control.Monad
import Control.Monad.State
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Data.OptDir
import Data.VectorSpace

import Data.Interval ((<=!), (>=!), (==!), (<!), (>!), (/=!))
import qualified Data.Interval as Interval

import ToySolver.Data.ArithRel
import qualified ToySolver.Data.LA as LA
import ToySolver.Data.Var
import qualified ToySolver.Simplex as Simplex
import qualified ToySolver.BoundsInference as BI

-- ---------------------------------------------------------------------------
-- Solver type

type Solver r = (Var, Simplex.Tableau r, VarSet, VarMap (LA.Expr r))

emptySolver :: VarSet -> Solver r
emptySolver vs = (1 + maximum ((-1) : IS.toList vs), Simplex.emptyTableau, IS.empty, IM.empty)

-- ---------------------------------------------------------------------------
-- LP Monad

type LP r = State (Solver r)

-- | Allocate a new /non-negative/ variable.
newVar :: LP r Var
newVar = do
  (x,tbl,avs,defs) <- get
  put (x+1,tbl,avs,defs)
  return x

getTableau :: LP r (Simplex.Tableau r)
getTableau = do
  (_,tbl,_,_) <- get
  return tbl

putTableau :: Simplex.Tableau r -> LP r ()
putTableau tbl = do
  (x,_,avs,defs) <- get
  put (x,tbl,avs,defs)

addArtificialVariable :: Var -> LP r ()
addArtificialVariable v = do
  (x,tbl,avs,defs) <- get
  put (x, tbl, IS.insert v avs, defs)

getArtificialVariables :: LP r VarSet
getArtificialVariables = do
  (_,_,avs,_) <- get
  return avs

clearArtificialVariables :: LP r ()
clearArtificialVariables = do
  (x,tbl,_,defs) <- get
  put (x, tbl, IS.empty, defs)

define :: Var -> LA.Expr r -> LP r ()
define v e = do
  (x,tbl,avs,defs) <- get
  put (x,tbl,avs, IM.insert v e defs)

getDefs :: LP r (VarMap (LA.Expr r))
getDefs = do
  (_,_,_,defs) <- get
  return defs

-- ---------------------------------------------------------------------------

-- | Add a contraint and maintain feasibility condition by introducing artificial variable (if necessary).
--
-- * Disequality is not supported.
-- 
-- * Unlike 'addConstraint', an equality contstraint becomes one row with an artificial variable.
-- 
addConstraintWithArtificialVariable :: Real r => LA.Atom r -> LP r ()
addConstraintWithArtificialVariable c = do
  c2 <- expandDefs' c
  let (e, rop, b) = normalizeConstraint c2
  assert (b >= 0) $ return ()
  tbl <- getTableau
  case rop of
    -- x≥0 is trivially true, since x is non-negative.
    Ge | b==0 && isSingleVar e -> return ()
    -- -x≤0 is trivially true, since x is non-negative.
    Le | b==0 && isSingleNegatedVar e -> return ()

    Le -> do
      v <- newVar -- slack variable
      putTableau $ Simplex.addRow tbl v (LA.coeffMap e, b)
    Ge -> do
      v1 <- newVar -- surplus variable
      v2 <- newVar -- artificial variable
      putTableau $ Simplex.addRow tbl v2 (LA.coeffMap (e ^-^ LA.var v1), b)
      addArtificialVariable v2
    Eql -> do
      v <- newVar -- artificial variable
      putTableau $ Simplex.addRow tbl v (LA.coeffMap e, b)
      addArtificialVariable v
    _ -> error $ "ToySolver.LPSolver.addConstraintWithArtificialVariable does not support " ++ show rop

-- | Add a contraint, without maintaining feasibilty condition of tableaus.
--
-- * Disequality is not supported.
--
-- * Unlike 'addConstraintWithArtificialVariable', an equality constraint becomes two rows.
-- 
addConstraint :: Real r => LA.Atom r -> LP r ()
addConstraint c = do
  ArithRel lhs rop rhs <- expandDefs' c
  let
    (b', e) = LA.extract LA.unitVar (lhs ^-^ rhs)
    b = - b'
  case rop of
    Le -> f e b
    Ge -> f (negateV e) (negate b)
    Eql -> do
      -- Unlike addConstraintWithArtificialVariable, an equality constraint becomes two rows.
      f e b
      f (negateV e) (negate b)
    _ -> error $ "ToySolver.LPSolver.addConstraint does not support " ++ show rop
  where
    -- -x≤b with b≥0 is trivially true.
    f e b | isSingleNegatedVar e && 0 <= b = return ()
    f e b = do
      tbl <- getTableau
      v <- newVar -- slack variable
      putTableau $ Simplex.addRow tbl v (LA.coeffMap e, b)

isSingleVar :: Real r => LA.Expr r -> Bool
isSingleVar e =
  case LA.terms e of
    [(1,_)] -> True
    _ -> False

isSingleNegatedVar :: Real r => LA.Expr r -> Bool
isSingleNegatedVar e =
  case LA.terms e of
    [(-1,_)] -> True
    _ -> False

expandDefs :: (Num r, Eq r) => LA.Expr r -> LP r (LA.Expr r)
expandDefs e = do
  defs <- getDefs
  return $ LA.applySubst defs e

expandDefs' :: (Num r, Eq r) => LA.Atom r -> LP r (LA.Atom r)
expandDefs' (ArithRel lhs op rhs) = do
  lhs' <- expandDefs lhs
  rhs' <- expandDefs rhs
  return $ ArithRel lhs' op rhs'

tableau :: (RealFrac r) => [LA.Atom r] -> LP r ()
tableau cs = do
  let (nonnegVars, cs') = collectNonnegVars cs IS.empty
      fvs = vars cs `IS.difference` nonnegVars
  forM_ (IS.toList fvs) $ \v -> do
    v1 <- newVar
    v2 <- newVar
    define v (LA.var v1 ^-^ LA.var v2)
  mapM_ addConstraint cs'

getModel :: Fractional r => VarSet -> LP r (Model r)
getModel vs = do
  tbl <- getTableau
  defs <- getDefs
  let vs' = (vs `IS.difference` IM.keysSet defs) `IS.union` IS.unions [vars e | e <- IM.elems defs]
      m0 = IM.fromAscList [(v, Simplex.currentValue tbl v) | v <- IS.toAscList vs']
  return $ IM.filterWithKey (\k _ -> k `IS.member` vs) $ IM.map (LA.evalExpr m0) defs `IM.union` m0

phaseI :: (Fractional r, Real r) => LP r Bool
phaseI = do
  introduceArtificialVariables
  tbl <- getTableau
  avs <- getArtificialVariables
  let (ret, tbl') = Simplex.phaseI tbl avs
  putTableau tbl'
  when ret clearArtificialVariables
  return ret

introduceArtificialVariables :: (Real r) => LP r ()
introduceArtificialVariables = do
  tbl <- getTableau
  tbl' <- liftM IM.fromList $ forM (IM.toList tbl) $ \(v,(e,rhs)) -> do
    if rhs >= 0 then do
      return (v,(e,rhs)) -- v + e == rhs
    else do
      a <- newVar
      addArtificialVariable a
      return (a, (IM.insert v (-1) (IM.map negate e), -rhs)) -- a - (v + e) == -rhs
  putTableau tbl'

simplex :: (Fractional r, Real r) => OptDir -> LA.Expr r -> LP r Bool
simplex optdir obj = do
  tbl <- getTableau
  defs <- getDefs
  let (ret, tbl') = Simplex.simplex optdir (Simplex.setObjFun tbl (LA.applySubst defs obj))
  putTableau tbl'
  return ret

dualSimplex :: (Fractional r, Real r) => OptDir -> LA.Expr r -> LP r Bool
dualSimplex optdir obj = do
  tbl <- getTableau
  defs <- getDefs
  let (ret, tbl') = Simplex.dualSimplex optdir (Simplex.setObjFun tbl (LA.applySubst defs obj))
  putTableau tbl'
  return ret

-- | results of optimization
data OptResult = Optimum | Unsat | Unbounded
  deriving (Show, Eq, Ord)

twoPhaseSimplex :: (Fractional r, Real r) => OptDir -> LA.Expr r -> LP r OptResult
twoPhaseSimplex optdir obj = do
  ret <- phaseI
  if not ret then
    return Unsat
  else do
    ret <- simplex optdir obj
    if ret then
      return Optimum
    else
      return Unbounded

primalDualSimplex :: (Fractional r, Real r) => OptDir -> LA.Expr r -> LP r OptResult
primalDualSimplex optdir obj = do
  tbl <- getTableau
  defs <- getDefs
  let (ret, tbl') = Simplex.primalDualSimplex optdir (Simplex.setObjFun tbl (LA.applySubst defs obj))
  putTableau tbl'
  if ret then
    return Optimum
  else if not (Simplex.isFeasible tbl') then
    return Unsat
  else
    return Unbounded

-- ---------------------------------------------------------------------------

-- convert right hand side to be non-negative
normalizeConstraint :: forall r. Real r => LA.Atom r -> (LA.Expr r, RelOp, r)
normalizeConstraint (ArithRel a op b)
  | rhs < 0   = (negateV lhs, flipOp op, negate rhs)
  | otherwise = (lhs, op, rhs)
  where
    (c, lhs) = LA.extract LA.unitVar (a ^-^ b)
    rhs = - c

collectNonnegVars :: forall r. (RealFrac r) => [LA.Atom r] -> VarSet -> (VarSet, [LA.Atom r])
collectNonnegVars cs ivs = (nonnegVars, cs)
  where
    vs = vars cs
    bounds = BI.inferBounds initialBounds cs ivs 1000
      where
        initialBounds = IM.fromAscList [(v, Interval.whole) | v <- IS.toAscList vs]
    nonnegVars = IS.filter (\v -> 0 <=! (bounds IM.! v)) vs

    isTriviallyTrue :: LA.Atom r -> Bool
    isTriviallyTrue (ArithRel a op b) =
      case op of
        Le -> i <=! 0
        Ge -> i >=! 0
        Lt -> i <! 0
        Gt -> i >! 0
        Eql -> i ==! 0
        NEq -> i /=! 0
      where
        i = LA.computeInterval bounds (a ^-^ b)

-- ---------------------------------------------------------------------------
