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
  ( Tableau
  , RowIndex
  , ColIndex
  , Row
  , PivotResult
  , objRow
  , pivot
  , lookupRow
  , setObjFun
  , currentObjValue
  , simplex
  , dualSimplex
  , phaseI
  , toCSV
  ) where

import Data.Function (on)
import Data.List (intersperse, minimumBy, foldl')
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Control.Exception

import Expr
import LC

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
pivot r s tbl =
    assert (validTableau tbl) $  -- precondition
    assert (validTableau tbl') $ -- postcondition
      tbl'
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
    row_r' = IM.map (/ a_rs) $ IM.insert r 1 $ IM.delete s row_r
    row_r_val' = row_r_val / a_rs
    row_s = (row_r', row_r_val')

lookupRow :: RowIndex -> Tableau r -> Row r
lookupRow r m = m IM.! r

-- 目的関数の行の基底変数の列が0になるように変形
normalizeObjRow :: Num r => Tableau r -> Row r -> Row r
normalizeObjRow a (row0,val0) = obj'
  where
    obj' = g $ foldl' f (IM.empty, val0) $ 
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

validTableau :: Tableau r -> Bool
validTableau tbl =
  and [v `IM.notMember` m | (v, (m,_)) <- IM.toList tbl, v /= objRow] &&
  and [IS.null (IM.keysSet m `IS.intersection` vs) | (v, (m,_)) <- IM.toList tbl']
  where
    tbl' = IM.delete objRow tbl
    vs = IM.keysSet tbl' 

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

phaseI :: (Real r, Fractional r) => Tableau r -> VarSet -> (Bool, Tableau r)
phaseI tbl avs
  | currentObjValue tbl1' /= 0 = (False, tbl1')
  | otherwise = (True, copyObjRow tbl $ removeArtificialVariables avs $ tbl1')
  where
    tbl1 = setObjFun tbl $ foldl' (.-.) (constLC 0) [(varLC v) | v <- IS.toList avs]
    tbl1' = go tbl1
    go tbl2
      | currentObjValue tbl2 == 0 = tbl2
      | otherwise = 
        case primalPivot False tbl2 of
          PivotSuccess tbl2' -> go tbl2'
          PivotFinished -> tbl2
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

toCSV :: Num r => (r -> String) -> Tableau r -> String
toCSV showCell tbl = unlines . map (concat . intersperse ",") $ header : body
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

    -- showCell x = show (fromRational (toRational x) :: Double)

    showRow i (row, row_val) = rowName i : [showCell (IM.findWithDefault 0 j row') | j <- cols] ++ [showCell row_val]
      where row' = IM.insert i 1 row
