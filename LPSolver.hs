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
import LC
import Simplex

-- ---------------------------------------------------------------------------

type Solver r = (Var, Tableau r, VarSet, VarMap (LC r))
type LP r = State (Solver r)

gensym :: LP r Var
gensym = do
  (x,tbl,avs,defs) <- get
  put (x+1,tbl,avs,defs)
  return x

addConstraint :: Real r => Constraint r -> LP r ()
addConstraint c = do
  let Rel2 lc rop b = normalizeConstraint c
  lc <- expandDefs lc -- FIXME 定数が復活してしまう可能性
  case rop of
    Le2 -> do
      v <- gensym -- slack variable
      (x,tbl,avs,defs) <- get
      put (x, IM.insert v (unLC lc, b) tbl, avs, defs)
    Ge2 -> do
      v1 <- gensym -- surplus variable
      v2 <- gensym -- artificial variable
      (x,tbl,avs,defs) <- get
      put (x, IM.insert v2 (unLC (lc .-. varLC v1), b) tbl, IS.insert v2 avs, defs)
    Eql2 -> do
      v <- gensym -- artificial variable
      (x,tbl,avs,defs) <- get
      put (x, IM.insert v (unLC lc, b) tbl, IS.insert v avs, defs)

expandDefs :: Num r => LC r -> LP r (LC r)
expandDefs e = do
  (_,_,_,defs) <- get
  return $ applySubst defs e

define :: Var -> LC r -> LP r ()
define v e = do
  (x,tbl,avs,defs) <- get
  put (x,tbl,avs, IM.insert v e defs)  

tableau :: (Fractional r, Real r) => [Constraint r] -> LP r ()
tableau cs = do
  let (nonnegVars, cs') = collectNonnegVars (map normalizeConstraint cs)
      fvs = vars (map (\(Rel2 x _ _) -> x) cs') `IS.difference` nonnegVars
  forM_ (IS.toList fvs) $ \v -> do
    v1 <- gensym
    v2 <- gensym
    define v (varLC v1 .-. varLC v2)
  mapM_ addConstraint cs'

getModel :: Fractional r => VarSet -> LP r (Model r)
getModel vs = do
  (_,tbl,_,defs) <- get
  let bs = IM.map snd (IM.delete objRow tbl)
      vs' = vs `IS.union` IS.fromList [v | e <- IM.elems defs, v <- IS.toList (fvLC e)]
      -- Note that IM.union is left-biased
      m0 = bs `IM.union` IM.fromList [(v,0) | v <- IS.toList vs']
  return $ IM.filterWithKey (\k _ -> k `IS.member` vs) $ IM.map (evalLC m0) defs `IM.union` m0

-- ---------------------------------------------------------------------------

data RelOp2 = Le2 | Ge2 | Eql2
    deriving (Show, Eq, Ord)

data Constraint r = Rel2 (LC r) RelOp2 r
    deriving (Show, Eq, Ord)

instance Variables (Constraint r) where
  vars (Rel2 a _ _) = vars a

compileExpr :: (Real r, Fractional r) => Expr r -> Maybe (LC r)
compileExpr (Const c) = return (constLC c)
compileExpr (Var c) = return (varLC c)
compileExpr (a :+: b) = liftM2 (.+.) (compileExpr a) (compileExpr b)
compileExpr (a :*: b) = do
  x <- compileExpr a
  y <- compileExpr b
  msum [ do{ c <- asConst x; return (c .*. y) }
       , do{ c <- asConst y; return (c .*. x) }
       ]
compileExpr (a :/: b) = do
  x <- compileExpr a
  c <- asConst =<< compileExpr b
  return $ (1/c) .*. x

compileAtom :: (Real r, Fractional r) => Atom r -> Maybe (Constraint r)
compileAtom (Rel a op b) = do
  a' <- compileExpr a
  b' <- compileExpr b
  op2 <- case op of
    Le  -> return Le2
    Ge  -> return Ge2
    Eql -> return Eql2
    Lt  -> Nothing
    Gt  -> Nothing
    NEq -> Nothing
  let LC m = a' .-. b'
  return $ Rel2 (LC (IM.delete constKey m)) op2 (- IM.findWithDefault 0 constKey m)

normalizeConstraint :: Real r => Constraint r -> Constraint r
normalizeConstraint (Rel2 a op b) = g a op b
  where
    g x Le2  y = if y < 0 then Rel2 (negateLC x) Ge2 (-y)  else Rel2 x Le2 y
    g x Ge2  y = if y < 0 then Rel2 (negateLC x) Le2 (-y)  else Rel2 x Ge2 y
    g x Eql2 y = if y < 0 then Rel2 (negateLC x) Eql2 (-y) else Rel2 x Eql2 y

collectNonnegVars :: forall r. (Fractional r, Real r) => [Constraint r] -> (VarSet, [Constraint r])
collectNonnegVars = foldr h (IS.empty, [])
  where
    h :: Constraint r -> (VarSet, [Constraint r]) -> (VarSet, [Constraint r])
    h cond (vs,cs) =
      case calcLB cond of
        Just (v, lb) | lb >= 0 -> (IS.insert v vs, if lb==0 then cs else cond:cs)
        _ -> (vs, cond:cs)

    calcLB :: Constraint r -> Maybe (Var,r)
    calcLB (Rel2 (LC m) Ge2 b) = 
      case IM.toList m of
        [(v,c)] | c > 0 -> Just (v, b / c)
        _ -> Nothing
    calcLB (Rel2 (LC m) Le2 b) =
      case IM.toList m of
        [(v,c)] | c < 0 -> Just (v, b / c)
        _ -> Nothing
    calcLB (Rel2 (LC m) Eql2 b) =
      case IM.toList m of
        [(v,c)] -> Just (v, b / c)
        _ -> Nothing

-- ---------------------------------------------------------------------------

solve' :: (Real r, Fractional r) => [Constraint r] -> SatResult r
solve' cs =
  flip evalState (1 + maximum ((-1) : IS.toList vs), IM.empty, IS.empty, IM.empty) $ do
    tableau cs
    (v,tbl,avs,defs) <- get
    case phaseI tbl avs of
      Nothing -> return $ Unsat
      Just tbl1 -> do
        put (v,tbl1,avs,defs)
        m <- getModel vs
        return $ Sat m
  where
    vs = vars cs

twoPhasedSimplex' :: (Real r, Fractional r) => Bool -> LC r -> [Constraint r] -> OptResult r
twoPhasedSimplex' isMinimize obj cs =
  flip evalState (1 + maximum ((-1) : IS.toList vs), IM.empty, IS.empty, IM.empty) $ do
    tableau cs
    (v,tbl,avs,defs) <- get    
    case phaseI tbl avs of
      Nothing -> return OptUnsat
      Just tbl1 -> 
        case simplex isMinimize (setObjFun tbl1 (applySubst defs obj)) of
          (True, tbl) -> do
             put (v,tbl,avs,defs)
             m <- getModel vs
             return $ Optimum (currentObjValue tbl) m
          (False, _) -> return $ Unbounded
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

toCSV :: (Real r, Fractional r) => Tableau r -> String
toCSV tbl = unlines . map (concat . intersperse ",") $ header : body
  where
    header :: [String]
    header = "" : map colName cols ++ [""]

    body :: [[String]]
    body = [showRow i (lookupRow i tbl) | i <- rows]

    rows :: [RowIndex]
    rows = IM.keys (IM.delete objRow tbl) ++ [objRow]

    cols :: [ColIndex]
    cols = [0..colMax]
      where
        colMax = maximum (-1 : [c | (row, _) <- IM.elems tbl, c <- IM.keys row])

    rowName :: RowIndex -> String
    rowName i = if i==objRow then "obj" else "x" ++ show i

    colName :: ColIndex -> String
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

