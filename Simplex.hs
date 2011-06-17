{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Simplex
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
module Simplex
  ( module Expr
  , module Formula
  , minimize
  , maximize
  , solve
  ) where

import Control.Monad
import Control.Monad.State
import Data.Function (on)
import Data.List (minimumBy, foldl', intersperse)
import Data.Maybe (fromMaybe)
import Data.Ratio
import Debug.Trace
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS

import Expr
import Formula
import LC

-- ---------------------------------------------------------------------------

data RelOp2 = Le2 | Ge2 | Eql2
    deriving (Show, Eq, Ord)

data Constraint r = Rel2 (LC r) RelOp2 r
    deriving (Show, Eq, Ord)

instance Variables (Constraint r) where
  vars (Rel2 a _ b) = vars a

compileExpr :: (Real r, Fractional r) => Expr r -> Maybe (LC r)
compileExpr (Const c) = return (constLC c)
compileExpr (Var c) = return (varLC c)
compileExpr (a :+: b) = liftM2 (.+.) (compileExpr a) (compileExpr b)
compileExpr (a :*: b) = do
  x <- compileExpr a
  y <- compileExpr b
  msum [ do{ c <- asConst x; return (scaleLC c y) }
       , do{ c <- asConst y; return (scaleLC c x) }
       ]
compileExpr (a :/: b) = do
  x <- compileExpr a
  c <- asConst =<< compileExpr b
  return $ scaleLC (1/c) x

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

-- ---------------------------------------------------------------------------

type Tableau r = VarMap (Row r)
{-
tbl ! v == (m, val)
==>
varLC v .+. m .==. constLC r
-}

type RowIndex = Int
type ColIndex = Int
type Row r = (VarMap r, r)
data PivotResult r = PivotUnbounded | PivotFinished | PivotSuccess (Tableau r)
  deriving (Show, Eq, Ord)

objRow :: RowIndex
objRow = -1

pivot :: Fractional r => RowIndex -> ColIndex -> Tableau r -> Tableau r
pivot r s tbl = tbl'
  where
    tbl' = IM.insert s row_s $ IM.map f $ IM.delete r $ tbl
    f orig@(row_i, row_i_val) =
      case IM.lookup s row_i of
        Nothing -> orig
        Just c ->
          ( IM.filter (0/=) $ IM.unionWith (+) (IM.delete s row_i) (IM.map (negate c *) row_r')
          , row_i_val - c*row_r_val'
          )
    (row_r, row_r_val) = lookupRow r tbl
    a_rs = row_r IM.! s
    row_r' = IM.map (/ a_rs) $ IM.delete s row_r
    row_r_val' = row_r_val / a_rs
    row_s = (IM.insert s 1 row_r', row_r_val')

lookupRow :: RowIndex -> Tableau r -> Row r
lookupRow r m = m IM.! r

-- 目的関数の行の基底変数の列が0になるように変形
normalizeObjRow :: Num r => Tableau r -> Row r -> Row r
normalizeObjRow a (row0,val0) = obj'
  where
    obj' = g $ foldl' f (IM.empty, 0) $ 
           [ case IM.lookup j a of
               Nothing -> (IM.singleton j x, 0)
               Just (row,val) -> (IM.map ((-x)*) (IM.delete j row), -x*val)
           | (j,x) <- IM.toList row0 ]
    f (m1,v1) (m2,v2) = (IM.unionWith (+) m1 m2, v1+v2)
    g (m,v) = (IM.filter (0/=) m, v)

setObjFun :: Num r => Tableau r -> LC r -> Tableau r
setObjFun tbl (LC m) = setObjRow tbl row
  where
    row = (IM.map negate (IM.delete constKey m), IM.findWithDefault 0 constKey m)

setObjRow :: Num r => Tableau r -> Row r -> Tableau r
setObjRow tbl row = IM.insert objRow (normalizeObjRow tbl row) tbl

copyObjRow :: Num r => Tableau r -> Tableau r -> Tableau r
copyObjRow from to =
  case IM.lookup objRow from of
    Nothing -> IM.delete objRow to
    Just row -> setObjRow to row

currentObjValue :: Num r => Tableau r -> r
currentObjValue = snd . lookupRow objRow

mkModel :: Fractional r => VarSet -> Tableau r -> Model r
mkModel xs tbl = bs `IM.union` nbs
  where
    bs = IM.map snd (IM.delete objRow tbl)
    nbs = IM.fromList [(x,0) | x <- IS.toList xs]

project :: Num r => VarSet -> VarMap (LC r) -> Model r -> Model r
project vs defs m = 
  IM.filterWithKey (\i _ -> i `IS.member` vs) $
  IM.map (evalLC m) defs `IM.union` m

-- ---------------------------------------------------------------------------
-- primal simplex

simplex :: (Real r, Fractional r) => Bool -> Tableau r -> (Bool, Tableau r)
simplex isMinimize = go
  where
    go tbl =
      case primalPivot isMinimize tbl of
        PivotFinished  -> (True, tbl)
        PivotUnbounded -> (False, tbl)
        PivotSuccess tbl' -> go tbl'

primalPivot :: (Real r, Fractional r) => Bool -> Tableau r -> PivotResult r
primalPivot isMinimize tbl
  | null cs   = PivotFinished
  | null rs   = PivotUnbounded
  | otherwise = PivotSuccess (pivot r s tbl)
  where
    cmp = if isMinimize then (0<) else (0>)
    cs = [(j,cj) | (j,cj) <- IM.toList (fst (lookupRow objRow tbl)), cmp cj]
    s = fst $ head cs
    rs = [ (i, y_i0 / y_is)
         | (i, (row_i, y_i0)) <- IM.toList tbl, i /= objRow
         , let y_is = IM.findWithDefault 0 s row_i, y_is > 0
         ]
    r = fst $ minimumBy (compare `on` snd) rs

-- ---------------------------------------------------------------------------
-- dual simplex

dualSimplex :: (Real r, Fractional r) => Bool -> Tableau r -> (Bool, Tableau r)
dualSimplex isMinimize = go
  where
    go tbl =
      case dualPivot isMinimize tbl of
        PivotFinished  -> (True, tbl)
        PivotUnbounded -> (False, tbl)
        PivotSuccess tbl' -> go tbl'

dualPivot :: (Real r, Fractional r) => Bool -> Tableau r -> PivotResult r
dualPivot isMinimize tbl
  | null rs   = PivotFinished
  | null cs   = PivotUnbounded
  | otherwise = PivotSuccess (pivot r s tbl)
  where
    cmp = if isMinimize then (0<) else (0>)
    rs = [(i, row_i) | (i, (row_i, y_i0)) <- IM.toList tbl, i /= objRow, cmp y_i0]
    (r, row_r) = head rs
    cs = [ (j, - y_0j / y_rj)
         | (j, y_rj) <- IM.toList row_r
         , y_rj < 0
         , let y_0j = IM.findWithDefault 0 j obj
         ]
    s = fst $ minimumBy (compare `on` snd) cs
    (obj,_) = lookupRow objRow tbl

-- ---------------------------------------------------------------------------
-- phase I of the two-phased method

phaseI :: (Real r, Fractional r) => Tableau r -> VarSet -> Maybe (Tableau r)
phaseI tbl avs
  | currentObjValue tbl1' /= 0 = Nothing
  | otherwise = Just $ copyObjRow tbl $ removeArtificialVariables avs $ tbl1'
  where
    tbl1 = setObjFun tbl $ foldl' (.-.) (constLC 0) [(varLC v) | v <- IS.toList avs]
    tbl1' = go tbl1
    go tbl
      | currentObjValue tbl == 0 = tbl
      | otherwise = 
        case primalPivot False tbl of
          PivotSuccess tbl' -> go tbl'
          PivotFinished -> tbl
          PivotUnbounded -> error "phaseI: should not happen"

-- post-processing of phaseI
-- pivotを使ってartificial variablesを基底から除いて、削除
removeArtificialVariables :: (Real r, Fractional r) => VarSet -> Tableau r -> Tableau r
removeArtificialVariables avs tbl0 = tbl2
  where
    tbl1 = foldl' f (IM.delete objRow tbl0) (IS.toList avs)
    tbl2 = IM.map (\(row,val) ->  (IM.filterWithKey (\j _ -> j `IS.notMember` avs) row, val)) tbl1
    f tbl i =
      case IM.lookup i tbl of
        Nothing -> tbl
        Just row ->
          case [j | (j,c) <- IM.toList (fst row), c /= 0, j `IS.notMember` avs] of
            [] -> IM.delete i tbl
            j:_ -> pivot i j tbl

-- ---------------------------------------------------------------------------

type M = State Var

gensym :: M Var
gensym = do{ x <- get; put (x+1); return x }

mkRow :: Num r => Constraint r -> M (Var, Row r, VarSet)
mkRow (Rel2 lc rop b) =
  case rop of
    Le2 -> do
      v <- gensym -- slack variable
      return ( v
             , (unLC lc, b)
             , IS.empty
             )
    Ge2 -> do
      v1 <- gensym -- surplus variable
      v2 <- gensym -- artificial variable
      return ( v2
             , (unLC (lc .-. varLC v1), b)
             , IS.singleton v2
             )
    Eql2 -> do
      v <- gensym -- artificial variable
      return ( v
             , (unLC lc, b)
             , IS.singleton v
             )

tableauM
  :: (Fractional r, Real r)
  => [Constraint r] -> M (Tableau r, VarSet, VarSet, VarMap (LC r))
tableauM cs = do
  let (nonnegVars, cs') = collectNonnegVars (map normalizeConstraint cs)
      fvs = vars (map (\(Rel2 x _ _) -> x) cs') `IS.difference` nonnegVars
  s <- liftM IM.fromList $ forM (IS.toList fvs) $ \v -> do
    v1 <- gensym
    v2 <- gensym
    return (v, varLC v1 .-. varLC v2)
  xs <- mapM mkRow $ map (\(Rel2 lc rop b) -> Rel2 (applySubst s lc) rop b) $ cs'
  let tbl = IM.fromList [(v, row) | (v, row, _) <- xs]
      avs = IS.unions [vs | (_, _, vs) <- xs]
      vs = IS.unions [nonnegVars, vars (IM.elems s), avs, IM.keysSet tbl]
  return (tbl,vs,avs,s)

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
  case phaseI tbl avs of
    Nothing -> Unsat
    Just tbl1 -> Sat (project vs defs (mkModel vs' tbl1))
  where
    vs = vars cs
    (tbl, vs', avs, defs) = tableau vs cs

twoPhasedSimplex' :: (Real r, Fractional r) => Bool -> LC r -> [Constraint r] -> OptResult r
twoPhasedSimplex' isMinimize obj cs =
  case phaseI tbl avs of
    Nothing -> OptUnsat
    Just tbl1 -> 
      case simplex isMinimize (setObjFun tbl1 (applySubst defs obj)) of
        (True, tbl) -> Optimum (currentObjValue tbl) (project vs defs (mkModel vs' tbl))
        (False, _) -> Unbounded
  where
    vs = vars cs `IS.union` vars obj
    (tbl, vs', avs, defs) = tableau vs cs

tableau :: (Fractional r, Real r) => VarSet -> [Constraint r] -> (Tableau r, VarSet, VarSet, VarMap (LC r))
tableau vs cs = flip evalState g $ tableauM cs
  where
    g = 1 + maximum ((-1) : IS.toList vs)

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
