{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  LPSolver
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- Naïve implementation of Simplex method
-- 
-- see http://www.math.cuhk.edu.hk/~wei/lpch3.pdf for detail
--
-----------------------------------------------------------------------------

module LPSolver where

import Control.Monad
import Control.Monad.State
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS

import Expr
import Formula
import LA
import Interval
import qualified Simplex
import qualified BoundsInference as BI

-- ---------------------------------------------------------------------------
-- LP Monad

type Solver r = (Var, Simplex.Tableau r, VarSet, VarMap (LC r))
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

define :: Var -> LC r -> LP r ()
define v e = do
  (x,tbl,avs,defs) <- get
  put (x,tbl,avs, IM.insert v e defs)

getDefs :: LP r (VarMap (LC r))
getDefs = do
  (_,_,_,defs) <- get
  return defs

-- ---------------------------------------------------------------------------

addConstraint :: Real r => Constraint r -> LP r ()
addConstraint c = do
  c <- expandDefs' c
  let (lc, rop, b) = normalizeConstraint c
  tbl <- getTableau
  case rop of
    -- x≥b で b≤0 なら追加しない。ad hoc なので一般化したい。
    Ge | isSingleVar lc && b<=0 -> return ()

    Le -> do
      v <- gensym -- slack variable
      putTableau $ Simplex.setRow v tbl (unLC lc, b)
    Ge -> do
      v1 <- gensym -- surplus variable
      v2 <- gensym -- artificial variable
      putTableau $ Simplex.setRow v2 tbl (unLC (lc .-. varLC v1), b)
      addArtificialVariable v2
    Eql -> do
      v <- gensym -- artificial variable
      putTableau $ Simplex.setRow v tbl (unLC lc, b)
      addArtificialVariable v
    _ -> error $ "addConstraint does not support " ++ show rop
  where
    isSingleVar (LC m) =
      case IM.toList m of
        [(_,1)] -> True
        _ -> False

addConstraint2 :: Real r => Constraint r -> LP r ()
addConstraint2 c = do
  (LARel lhs rop rhs) <- expandDefs' c
  let
    LC m = lhs .-. rhs
    lc = LC (IM.delete constKey m)
    b = - IM.findWithDefault 0 constKey m
  tbl <- getTableau
  case rop of
    Le -> f lc b
    Ge -> f (lnegate lc) (negate b)
    Eql -> do
      f lc b
      f (lnegate lc) (negate b)
    _ -> error $ "addConstraint does not support " ++ show rop
  where
    -- -x≤b で -b≤0 なら追加しない。ad hoc なので一般化したい。
    f lc b  | isSingleNegatedVar lc && -b <= 0 = return ()
    f lc b = do
      tbl <- getTableau
      v <- gensym -- slack variable
      putTableau $ Simplex.setRow v tbl (unLC lc, b)

    isSingleNegatedVar (LC m) =
      case IM.toList m of
        [(_,-1)] -> True
        _ -> False

expandDefs :: Num r => LC r -> LP r (LC r)
expandDefs e = do
  defs <- getDefs
  return $ applySubst defs e

expandDefs' :: Num r => Constraint r -> LP r (Constraint r)
expandDefs' (LARel lhs op rhs) = do
  lhs' <- expandDefs lhs
  rhs' <- expandDefs rhs
  return $ LARel lhs' op rhs'

tableau :: (RealFrac r) => [Constraint r] -> LP r ()
tableau cs = do
  let (nonnegVars, cs') = collectNonnegVars cs IS.empty
      fvs = vars cs `IS.difference` nonnegVars
  forM_ (IS.toList fvs) $ \v -> do
    v1 <- gensym
    v2 <- gensym
    define v (varLC v1 .-. varLC v2)
  mapM_ addConstraint cs'

getModel :: Fractional r => VarSet -> LP r (Model r)
getModel vs = do
  tbl <- getTableau
  defs <- getDefs
  let bs = IM.map snd (IM.delete Simplex.objRow tbl)
      vs' = vs `IS.union` IS.fromList [v | e <- IM.elems defs, v <- IS.toList (fvLC e)]
      -- Note that IM.union is left-biased
      m0 = bs `IM.union` IM.fromList [(v,0) | v <- IS.toList vs']
  return $ IM.filterWithKey (\k _ -> k `IS.member` vs) $ IM.map (evalLC m0) defs `IM.union` m0

phaseI :: (Fractional r, Real r) => LP r Bool
phaseI = do
  tbl <- getTableau
  avs <- getArtificialVariables
  let (ret, tbl') = Simplex.phaseI tbl avs
  putTableau tbl'
  when ret clearArtificialVariables
  return ret

simplex :: (Fractional r, Real r) => Bool -> LC r -> LP r Bool
simplex isMinimize obj = do
  tbl <- getTableau
  defs <- getDefs
  let (ret, tbl') = Simplex.simplex isMinimize (Simplex.setObjFun tbl (applySubst defs obj))
  putTableau tbl'
  return ret

dualSimplex :: (Fractional r, Real r) => Bool -> LC r -> LP r Bool
dualSimplex isMinimize obj = do
  tbl <- getTableau
  defs <- getDefs
  let (ret, tbl') = Simplex.dualSimplex isMinimize (Simplex.setObjFun tbl (applySubst defs obj))
  putTableau tbl'
  return ret

-- ---------------------------------------------------------------------------

normalizeConstraint :: forall r. Real r => Constraint r -> (LC r, RelOp, r)
normalizeConstraint (LARel a op b)
  | rhs < 0   = (lnegate lhs, flipOp op, negate rhs)
  | otherwise = (lhs, op, rhs)
  where
    LC m = a .-. b
    rhs = - IM.findWithDefault 0 constKey m
    lhs = LC (IM.delete constKey m)

collectNonnegVars :: forall r. (RealFrac r) => [Constraint r] -> VarSet -> (VarSet, [Constraint r])
collectNonnegVars cs ivs = (nonnegVars, cs)
  where
    vs = vars cs
    bounds = BI.inferBounds initialBounds cs ivs 1000
      where
        initialBounds = IM.fromList [(v, Interval.univ) | v <- IS.toList vs]
    nonnegVars = IS.filter f vs
      where
        f v = case bounds IM.! v of
                Interval (Just (_, lb)) _ | 0 <= lb -> True
                _ -> False

    isTriviallyTrue :: Constraint r -> Bool
    isTriviallyTrue (LARel a op b) =
      case op of
        Le ->
          case ub of
            Nothing -> False
            Just (_, val) -> val <= 0
        Ge ->
          case lb of
            Nothing -> False
            Just (_, val) -> val >= 0
        Lt ->
          case ub of
            Nothing -> False
            Just (incl, val) -> val < 0 || (not incl && val <= 0)
        Gt ->
          case lb of
            Nothing -> False
            Just (incl, val) -> val > 0 || (not incl && val >= 0)
        Eql -> isTriviallyTrue (LARel c Le lzero) && isTriviallyTrue (LARel c Ge lzero)
        NEq -> isTriviallyTrue (LARel c Lt lzero) && isTriviallyTrue (LARel c Gt lzero)
      where
        c = a .-. b
        Interval lb ub = BI.evalToInterval bounds c

-- ---------------------------------------------------------------------------
