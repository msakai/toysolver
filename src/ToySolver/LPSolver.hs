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
  , addConstraint2
  , tableau
  , define

  -- * Solving
  , phaseI
  , simplex
  , dualSimplex
  , OptResult (..)
  , twoPhaseSimplex

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

-- | Note that @addConstraint@ maintains feasbility by introducing artificial variables
addConstraint :: Real r => LA.Atom r -> LP r ()
addConstraint c = do
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
    _ -> error $ "ToySolver.LPSolver.addConstraint does not support " ++ show rop

-- | Unlike @addConstraint@, @addConstraint2@ does not maintain feasibility.
addConstraint2 :: Real r => LA.Atom r -> LP r ()
addConstraint2 c = do
  Rel lhs rop rhs <- expandDefs' c
  let
    (b', e) = LA.extract LA.unitVar (lhs ^-^ rhs)
    b = - b'
  case rop of
    Le -> f e b
    Ge -> f (negateV e) (negate b)
    Eql -> do
      -- Unlike addConstraint, an equality constraint becomes two rows.
      f e b
      f (negateV e) (negate b)
    _ -> error $ "ToySolver.LPSolver.addConstraint2 does not support " ++ show rop
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
expandDefs' (Rel lhs op rhs) = do
  lhs' <- expandDefs lhs
  rhs' <- expandDefs rhs
  return $ Rel lhs' op rhs'

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
  tbl <- getTableau
  avs <- getArtificialVariables
  let (ret, tbl') = Simplex.phaseI tbl avs
  putTableau tbl'
  when ret clearArtificialVariables
  return ret

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

-- ---------------------------------------------------------------------------

-- convert right hand side to be non-negative
normalizeConstraint :: forall r. Real r => LA.Atom r -> (LA.Expr r, RelOp, r)
normalizeConstraint (Rel a op b)
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
        initialBounds = IM.fromList [(v, Interval.whole) | v <- IS.toList vs]
    nonnegVars = IS.filter f vs
      where
        f v = case Interval.lowerBound (bounds IM.! v) of
                Interval.Finite lb | 0 <= lb -> True
                _ -> False

    isTriviallyTrue :: LA.Atom r -> Bool
    isTriviallyTrue (Rel a op b) =
      case op of
        Le ->
          case ub of
            Interval.PosInf -> False
            Interval.Finite val -> val <= 0
            Interval.NegInf -> True -- should not happen
        Ge ->
          case lb of
            Interval.NegInf -> False
            Interval.Finite val -> val >= 0
            Interval.PosInf -> True -- should not happen
        Lt ->
          case ub of
            Interval.PosInf -> False
            Interval.Finite val -> val < 0 || (not inUB && val <= 0)
            Interval.NegInf -> True -- should not happen
        Gt ->
          case lb of
            Interval.NegInf -> False
            Interval.Finite val -> val > 0 || (not inLB && val >= 0)
            Interval.PosInf -> True -- should not happen
        Eql -> isTriviallyTrue (c .<=. zeroV) && isTriviallyTrue (c .>=. zeroV)
        NEq -> isTriviallyTrue (c .<. zeroV) || isTriviallyTrue (c .>. zeroV)
      where
        c = a ^-^ b
        i = LA.computeInterval bounds c
        (lb, inLB) = Interval.lowerBound' i
        (ub, inUB) = Interval.upperBound' i

-- ---------------------------------------------------------------------------
