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

module LPSolver
  ( module Expr
  , module Formula
  , minimize
  , maximize
  , solve
  ) where

import Control.Monad
import Control.Monad.State
import Data.List (intersperse)
import Data.Maybe (fromMaybe)
import Data.Ratio
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
      putTableau $ IM.insert v (unLC lc, b) tbl
    Ge -> do
      v1 <- gensym -- surplus variable
      v2 <- gensym -- artificial variable
      putTableau $ IM.insert v2 (unLC (lc .-. varLC v1), b) tbl
      addArtificialVariable v2
    Eql -> do
      v <- gensym -- artificial variable
      putTableau $ IM.insert v (unLC lc, b) tbl
      addArtificialVariable v
    _ -> error $ "addConstraint does not support " ++ show rop
  where
    isSingleVar (LC m) =
      case IM.toList m of
        [(v,1)] -> True
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

tableau :: (Real r, Fractional r) => [Constraint r] -> LP r ()
tableau cs = do
  let (nonnegVars, cs') = collectNonnegVars cs
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

-- ---------------------------------------------------------------------------

normalizeConstraint :: forall r. Real r => Constraint r -> (LC r, RelOp, r)
normalizeConstraint (LARel a op b)
  | rhs < 0   = (negateLC lhs, flipOp op, negate rhs)
  | otherwise = (lhs, op, rhs)
  where
    LC m = a .-. b
    rhs = - IM.findWithDefault 0 constKey m
    lhs = LC (IM.delete constKey m)

collectNonnegVars :: forall r. (Fractional r, Real r) => [Constraint r] -> (VarSet, [Constraint r])
collectNonnegVars cs = (nonnegVars, cs)
  where
    vs = vars cs
    bounds = BI.inferBounds initialBounds cs
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
        Eql -> isTriviallyTrue (LARel c Le zero) && isTriviallyTrue (LARel c Ge zero)
        NEq -> isTriviallyTrue (LARel c Lt zero) && isTriviallyTrue (LARel c Gt zero)
      where
        c = a .-. b
        Interval lb ub = BI.evalToInterval bounds c

-- ---------------------------------------------------------------------------

solve' :: (Real r, Fractional r) => [Constraint r] -> SatResult r
solve' cs =
  flip evalState (1 + maximum ((-1) : IS.toList vs), IM.empty, IS.empty, IM.empty) $ do
    tableau cs
    ret <- phaseI
    if not ret
      then return Unsat
      else do
        m <- getModel vs
        return (Sat m)
  where
    vs = vars cs

twoPhasedSimplex' :: (Real r, Fractional r) => Bool -> LC r -> [Constraint r] -> OptResult r
twoPhasedSimplex' isMinimize obj cs =
  flip evalState (1 + maximum ((-1) : IS.toList vs), IM.empty, IS.empty, IM.empty) $ do
    tableau cs
    ret <- phaseI
    if not ret
      then return OptUnsat
      else do
        ret2 <- simplex isMinimize obj
        if not ret2
          then return Unbounded
          else do
             m <- getModel vs
             tbl <- getTableau 
             return $ Optimum (Simplex.currentObjValue tbl) m
  where
    vs = vars cs `IS.union` vars obj

-- ---------------------------------------------------------------------------
-- High Level interface

maximize :: (Real r, Fractional r) => Expr r -> [Atom r] -> OptResult r
maximize = optimize False

minimize :: (Real r, Fractional r) => Expr r -> [Atom r] -> OptResult r
minimize = optimize True

optimize :: (Real r, Fractional r) => Bool -> Expr r -> [Atom r] -> OptResult r
optimize isMinimize obj2 cs2 = fromMaybe OptUnknown $ do
  obj <- compileExpr obj2  
  cs <- mapM compileAtom cs2
  return (twoPhasedSimplex' isMinimize obj cs)

solve :: (Real r, Fractional r) => [Atom r] -> SatResult r
solve cs2 = fromMaybe Unknown $ do
  cs <- mapM compileAtom cs2
  return (solve' cs)

-- ---------------------------------------------------------------------------

toCSV :: (Real r, Fractional r) => Simplex.Tableau r -> String
toCSV tbl = unlines . map (concat . intersperse ",") $ header : body
  where
    header :: [String]
    header = "" : map colName cols ++ [""]

    body :: [[String]]
    body = [showRow i (Simplex.lookupRow i tbl) | i <- rows]

    rows :: [Simplex.RowIndex]
    rows = IM.keys (IM.delete Simplex.objRow tbl) ++ [Simplex.objRow]

    cols :: [Simplex.ColIndex]
    cols = [0..colMax]
      where
        colMax = maximum (-1 : [c | (row, _) <- IM.elems tbl, c <- IM.keys row])

    rowName :: Simplex.RowIndex -> String
    rowName i = if i==Simplex.objRow then "obj" else "x" ++ show i

    colName :: Simplex.ColIndex -> String
    colName j = "x" ++ show j

    showCell x = show (fromRational (toRational x) :: Double)
    showRow i (row, row_val) = rowName i : [showCell (IM.findWithDefault 0 j row) | j <- cols] ++ [showCell row_val]

-- ---------------------------------------------------------------------------

example_3_2 :: (Expr Rational, [Atom Rational])
example_3_2 = (obj, cond)
  where
    x1 = var 1
    x2 = var 2
    x3 = var 3
    obj = 3*x1 + 2*x2 + 3*x3
    cond = [ 2*x1 +   x2 +   x3 .<=. 2
           ,   x1 + 2*x2 + 3*x3 .<=. 5
           , 2*x1 + 2*x2 +   x3 .<=. 6
           , x1 .>=. 0
           , x2 .>=. 0
           , x3 .>=. 0
           ]

test_3_2 :: Bool
test_3_2 =
  uncurry maximize example_3_2 == 
  Optimum (27 % 5) (IM.fromList [(1,1 % 5),(2,0 % 1),(3,8 % 5)])

example_3_5 :: (Expr Rational, [Atom Rational])
example_3_5 = (obj, cond)
  where
    x1 = var 1
    x2 = var 2
    x3 = var 3
    x4 = var 4
    x5 = var 5
    obj = -2*x1 + 4*x2 + 7*x3 + x4 + 5*x5
    cond = [ -x1 +   x2 + 2*x3 +   x4 + 2*x5 .==. 7
           , -x1 + 2*x2 + 3*x3 +   x4 +   x5 .==. 6
           , -x1 +   x2 +   x3 + 2*x4 +   x5 .==. 4
           , x2 .>=. 0
           , x3 .>=. 0
           , x4 .>=. 0
           , x5 .>=. 0
           ]

test_3_5 :: Bool
test_3_5 =
  uncurry minimize example_3_5 ==
  Optimum (19 % 1) (IM.fromList [(1,(-1) % 1),(2,0 % 1),(3,1 % 1),(4,0 % 1),(5,2 % 1)]) 

example_4_1 :: (Expr Rational, [Atom Rational])
example_4_1 = (obj, cond)
  where
    x1 = var 1
    x2 = var 2
    obj = 2*x1 + x2
    cond = [ -x1 + x2 .>=. 2
           ,  x1 + x2 .<=. 1
           , x1 .>=. 0
           , x2 .>=. 0
           ]

test_4_1 :: Bool
test_4_1 =
  uncurry maximize example_4_1 ==
  OptUnsat

example_4_2 :: (Expr Rational, [Atom Rational])
example_4_2 = (obj, cond)
  where
    x1 = var 1
    x2 = var 2
    obj = 2*x1 + x2
    cond = [ - x1 - x2 .<=. 10
           , 2*x1 - x2 .<=. 40
           , x1 .>=. 0
           , x2 .>=. 0
           ]

test_4_2 :: Bool
test_4_2 =
  uncurry maximize example_4_2 ==
  Unbounded

example_4_3 :: (Expr Rational, [Atom Rational])
example_4_3 = (obj, cond)
  where
    x1 = var 1
    x2 = var 2
    obj = 6*x1 - 2*x2
    cond = [ 2*x1 - x2 .<=. 2
           , x1 .<=. 4
           , x1 .>=. 0
           , x2 .>=. 0
           ]

test_4_3 :: Bool
test_4_3 =
  uncurry maximize example_4_3 ==
  Optimum (12 % 1) (IM.fromList [(1,4 % 1),(2,6 % 1)])

example_4_5 :: (Expr Rational, [Atom Rational])
example_4_5 = (obj, cond)
  where
    x1 = var 1
    x2 = var 2
    obj = 2*x1 + x2
    cond = [ 4*x1 + 3*x2 .<=. 12
           , 4*x1 +   x2 .<=. 8
           , 4*x1 -   x2 .<=. 8
           , x1 .>=. 0
           , x2 .>=. 0
           ]

test_4_5 :: Bool
test_4_5 =
  uncurry maximize example_4_5 ==
  Optimum (5 % 1) (IM.fromList [(1,3 % 2),(2,2 % 1)])

example_4_6 :: (Expr Rational, [Atom Rational])
example_4_6 = (obj, cond)
  where
    x1 = var 1
    x2 = var 2
    x3 = var 3
    x4 = var 4
    obj = 20*x1 + (1/2)*x2 - 6*x3 + (3/4)*x4
    cond = [    x1 .<=. 2
           ,  8*x1 -       x2 + 9*x3 + (1/4)*x4 .<=. 16
           , 12*x1 - (1/2)*x2 + 3*x3 + (1/2)*x4 .<=. 24
           , x2 .<=. 1
           , x1 .>=. 0
           , x2 .>=. 0
           , x3 .>=. 0
           , x4 .>=. 0
           ]

test_4_6 :: Bool
test_4_6 =
  uncurry maximize example_4_6 ==
  Optimum (165 % 4) (IM.fromList [(1,2 % 1),(2,1 % 1),(3,0 % 1),(4,1 % 1)])

example_4_7 :: (Expr Rational, [Atom Rational])
example_4_7 = (obj, cond)
  where
    x1 = var 1
    x2 = var 2
    x3 = var 3
    x4 = var 4
    obj = x1 + 1.5*x2 + 5*x3 + 2*x4
    cond = [ 3*x1 + 2*x2 +   x3 + 4*x4 .<=. 6
           , 2*x1 +   x2 + 5*x3 +   x4 .<=. 4
           , 2*x1 + 6*x2 - 4*x3 + 8*x4 .==. 0
           ,   x1 + 3*x2 - 2*x3 + 4*x4 .==. 0
           , x1 .>=. 0
           , x2 .>=. 0
           , x3 .>=. 0
           , x4 .>=. 0
           ]

test_4_7 :: Bool
test_4_7 =
  uncurry maximize example_4_7 ==
  Optimum (48 % 11) (IM.fromList [(1,0 % 1),(2,0 % 1),(3,8 % 11),(4,4 % 11)])

testAll :: Bool
testAll = and
  [ test_3_2
  , test_3_5
  , test_4_1
  , test_4_2
  , test_4_3
  , test_4_5
  , test_4_6
  , test_4_7
  ]

-- ---------------------------------------------------------------------------

