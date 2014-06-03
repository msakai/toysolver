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

module ToySolver.LPSolver where

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
-- LP Monad

type Solver r = (Var, Simplex.Tableau r, VarSet, VarMap (LA.Expr r))
type LP r = State (Solver r)

emptySolver :: VarSet -> Solver r
emptySolver vs = (1 + maximum ((-1) : IS.toList vs), IM.empty, IS.empty, IM.empty)

gensym :: LP r Var
gensym = do
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

addConstraint :: Real r => LA.Atom r -> LP r ()
addConstraint c = do
  c2 <- expandDefs' c
  let (e, rop, b) = normalizeConstraint c2
  tbl <- getTableau
  case rop of
    -- x≥b で b≤0 なら追加しない。ad hoc なので一般化したい。
    Ge | isSingleVar e && b<=0 -> return ()

    Le -> do
      v <- gensym -- slack variable
      putTableau $ Simplex.setRow v tbl (LA.coeffMap e, b)
    Ge -> do
      v1 <- gensym -- surplus variable
      v2 <- gensym -- artificial variable
      putTableau $ Simplex.setRow v2 tbl (LA.coeffMap (e ^-^ LA.var v1), b)
      addArtificialVariable v2
    Eql -> do
      v <- gensym -- artificial variable
      putTableau $ Simplex.setRow v tbl (LA.coeffMap e, b)
      addArtificialVariable v
    _ -> error $ "ToySolver.LPSolver.addConstraint does not support " ++ show rop
  where
    isSingleVar e =
      case LA.terms e of
        [(1,_)] -> True
        _ -> False

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
      f e b
      f (negateV e) (negate b)
    _ -> error $ "ToySolver.LPSolver.addConstraint2 does not support " ++ show rop
  where
    -- -x≤b で -b≤0 なら追加しない。ad hoc なので一般化したい。
    f e b  | isSingleNegatedVar e && -b <= 0 = return ()
    f e b = do
      tbl <- getTableau
      v <- gensym -- slack variable
      putTableau $ Simplex.setRow v tbl (LA.coeffMap e, b)

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
    v1 <- gensym
    v2 <- gensym
    define v (LA.var v1 ^-^ LA.var v2)
  mapM_ addConstraint cs'

getModel :: Fractional r => VarSet -> LP r (Model r)
getModel vs = do
  tbl <- getTableau
  defs <- getDefs
  let bs = IM.map snd (IM.delete Simplex.objRow tbl)
      vs' = vs `IS.union` IS.fromList [v | e <- IM.elems defs, v <- IS.toList (vars e)]
      -- Note that IM.union is left-biased
      m0 = bs `IM.union` IM.fromList [(v,0) | v <- IS.toList vs']
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

-- ---------------------------------------------------------------------------

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
