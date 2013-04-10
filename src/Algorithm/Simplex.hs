{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Algorithm.Simplex
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
module Algorithm.Simplex
  ( module Data.OptDir
  , Tableau
  , RowIndex
  , ColIndex
  , Row
  , PivotResult
  , objRow
  , pivot
  , lookupRow
  , setRow
  , setObjFun
  , currentObjValue
  , simplex
  , dualSimplex
  , phaseI
  , toCSV
  ) where

import Data.Ord
import Data.List (intersperse, minimumBy, foldl')
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Data.OptDir
import Data.VectorSpace
import Control.Exception

import qualified Data.LA as LA
import Data.Var

-- ---------------------------------------------------------------------------

type Tableau r = VarMap (Row r)
{-
tbl ! v == (m, val)
==>
var v .+. m .==. constant val
-}

type RowIndex = Int
type ColIndex = Int
type Row r = (VarMap r, r)
data PivotResult r = PivotUnbounded | PivotFinished | PivotSuccess (Tableau r)
  deriving (Show, Eq, Ord)

objRow :: RowIndex
objRow = -1

pivot :: (Fractional r, Eq r) => RowIndex -> ColIndex -> Tableau r -> Tableau r
{-# INLINE pivot #-}
{-# SPECIALIZE pivot :: RowIndex -> ColIndex -> Tableau Rational -> Tableau Rational #-}
{-# SPECIALIZE pivot :: RowIndex -> ColIndex -> Tableau Double -> Tableau Double #-}
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

-- 行の基底変数の列が0になるように変形
normalizeRow :: (Num r, Eq r) => Tableau r -> Row r -> Row r
normalizeRow a (row0,val0) = obj'
  where
    obj' = g $ foldl' f (IM.empty, val0) $ 
           [ case IM.lookup j a of
               Nothing -> (IM.singleton j x, 0)
               Just (row,val) -> (IM.map ((-x)*) (IM.delete j row), -x*val)
           | (j,x) <- IM.toList row0 ]
    f (m1,v1) (m2,v2) = (IM.unionWith (+) m1 m2, v1+v2)
    g (m,v) = (IM.filter (0/=) m, v)

setRow :: (Num r, Eq r) => RowIndex -> Tableau r -> Row r -> Tableau r
setRow i tbl row = assert (validTableau tbl) $ assert (validTableau tbl') $ tbl'
  where
    tbl' = IM.insert i (normalizeRow tbl row) tbl

setObjFun :: (Num r, Eq r) => Tableau r -> LA.Expr r -> Tableau r
setObjFun tbl e = setRow objRow tbl row
  where
    row =
      case LA.extract LA.unitVar e of
        (c, e') -> (LA.coeffMap (negateV e'), c)

copyObjRow :: (Num r, Eq r) => Tableau r -> Tableau r -> Tableau r
copyObjRow from to =
  case IM.lookup objRow from of
    Nothing -> IM.delete objRow to
    Just row -> setRow objRow to row

currentObjValue :: (Num r, Eq r) => Tableau r -> r
currentObjValue = snd . lookupRow objRow

validTableau :: Tableau r -> Bool
validTableau tbl =
  and [v `IM.notMember` m | (v, (m,_)) <- IM.toList tbl, v /= objRow] &&
  and [IS.null (IM.keysSet m `IS.intersection` vs) | (m,_) <- IM.elems tbl']
  where
    tbl' = IM.delete objRow tbl
    vs = IM.keysSet tbl' 

isFeasible :: Real r => Tableau r -> Bool
isFeasible tbl = 
  and [val >= 0 | (v, (_,val)) <- IM.toList tbl, v /= objRow]

isOptimal :: Real r => OptDir -> Tableau r -> Bool
isOptimal optdir tbl =
  and [not (cmp cj) | cj <- IM.elems (fst (lookupRow objRow tbl))]
  where
    cmp = case optdir of
            OptMin -> (0<)
            OptMax -> (0>)

isImproving :: Real r => OptDir -> Tableau r -> Tableau r -> Bool
isImproving OptMin from to = currentObjValue to <= currentObjValue from 
isImproving OptMax from to = currentObjValue to >= currentObjValue from 

-- ---------------------------------------------------------------------------
-- primal simplex

simplex :: (Real r, Fractional r) => OptDir -> Tableau r -> (Bool, Tableau r)
{-# SPECIALIZE simplex :: OptDir -> Tableau Rational -> (Bool, Tableau Rational) #-}
{-# SPECIALIZE simplex :: OptDir -> Tableau Double -> (Bool, Tableau Double) #-}
simplex optdir = go
  where
    go tbl = assert (isFeasible tbl) $
      case primalPivot optdir tbl of
        PivotFinished  -> assert (isOptimal optdir tbl) (True, tbl)
        PivotUnbounded -> (False, tbl)
        PivotSuccess tbl' -> assert (isImproving optdir tbl tbl') $ go tbl'

primalPivot :: (Real r, Fractional r) => OptDir -> Tableau r -> PivotResult r
{-# INLINE primalPivot #-}
primalPivot optdir tbl
  | null cs   = PivotFinished
  | null rs   = PivotUnbounded
  | otherwise = PivotSuccess (pivot r s tbl)
  where
    cmp = case optdir of
            OptMin -> (0<)
            OptMax -> (0>)
    cs = [(j,cj) | (j,cj) <- IM.toList (fst (lookupRow objRow tbl)), cmp cj]
    -- smallest subscript rule
    s = fst $ head cs
    -- classical rule
    --s = fst $ (if optdir==OptMin then maximumBy else minimumBy) (compare `on` snd) cs
    rs = [ (i, y_i0 / y_is)
         | (i, (row_i, y_i0)) <- IM.toList tbl, i /= objRow
         , let y_is = IM.findWithDefault 0 s row_i, y_is > 0
         ]
    r = fst $ minimumBy (comparing snd) rs

-- ---------------------------------------------------------------------------
-- dual simplex

dualSimplex :: (Real r, Fractional r) => OptDir -> Tableau r -> (Bool, Tableau r)
{-# SPECIALIZE dualSimplex :: OptDir -> Tableau Rational -> (Bool, Tableau Rational) #-}
{-# SPECIALIZE dualSimplex :: OptDir -> Tableau Double -> (Bool, Tableau Double) #-}
dualSimplex optdir = go
  where
    go tbl = assert (isOptimal optdir tbl) $
      case dualPivot optdir tbl of
        PivotFinished  -> assert (isFeasible tbl) $ (True, tbl)
        PivotUnbounded -> (False, tbl)
        PivotSuccess tbl' -> assert (isImproving optdir tbl' tbl) $ go tbl'

dualPivot :: (Real r, Fractional r) => OptDir -> Tableau r -> PivotResult r
{-# INLINE dualPivot #-}
dualPivot optdir tbl
  | null rs   = PivotFinished
  | null cs   = PivotUnbounded
  | otherwise = PivotSuccess (pivot r s tbl)
  where
    rs = [(i, row_i) | (i, (row_i, y_i0)) <- IM.toList tbl, i /= objRow, 0 > y_i0]
    (r, row_r) = head rs
    cs = [ (j, if optdir==OptMin then y_0j / y_rj else - y_0j / y_rj)
         | (j, y_rj) <- IM.toList row_r
         , y_rj < 0
         , let y_0j = IM.findWithDefault 0 j obj
         ]
    s = fst $ minimumBy (comparing snd) cs
    (obj,_) = lookupRow objRow tbl

-- ---------------------------------------------------------------------------
-- phase I of the two-phased method

phaseI :: (Real r, Fractional r) => Tableau r -> VarSet -> (Bool, Tableau r)
{-# SPECIALIZE phaseI :: Tableau Rational -> VarSet -> (Bool, Tableau Rational) #-}
{-# SPECIALIZE phaseI :: Tableau Double -> VarSet -> (Bool, Tableau Double) #-}
phaseI tbl avs
  | currentObjValue tbl1' /= 0 = (False, tbl1')
  | otherwise = (True, copyObjRow tbl $ removeArtificialVariables avs $ tbl1')
  where
    optdir = OptMax
    tbl1 = setObjFun tbl $ negateV $ sumV [LA.var v | v <- IS.toList avs]
    tbl1' = go tbl1
    go tbl2
      | currentObjValue tbl2 == 0 = tbl2
      | otherwise = 
        case primalPivot optdir tbl2 of
          PivotSuccess tbl2' -> assert (isImproving optdir tbl2 tbl2') $ go tbl2'
          PivotFinished -> assert (isOptimal optdir tbl2) tbl2
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

toCSV :: (Num r, Eq r, Show r) => (r -> String) -> Tableau r -> String
toCSV showCell tbl = unlines . map (concat . intersperse ",") $ header : body
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

    showRow i (row, row_val) = rowName i : [showCell (IM.findWithDefault 0 j row') | j <- cols] ++ [showCell row_val]
      where row' = IM.insert i 1 row

-- ---------------------------------------------------------------------------

-- 退化して巡回の起こるKuhnの7変数3制約の例

kuhn_7_3 :: Tableau Rational
kuhn_7_3 = IM.fromList
  [ (1, (IM.fromList [(4,-2), (5,-9), (6,1), (7,9)],       0))
  , (2, (IM.fromList [(4,1/3), (5,1), (6,-1/3), (7,-2)],   0))
  , (3, (IM.fromList [(4,2), (5,3), (6,-1), (7,-12)],      2))
  , (objRow, (IM.fromList [(4,2), (5,3), (6,-1), (7,-12)], 0))
  ]

test_kuhn_7_3 :: (Bool, Tableau Rational)
test_kuhn_7_3 = simplex OptMin kuhn_7_3

-- from http://www.math.cuhk.edu.hk/~wei/lpch5.pdf
example_5_7 :: Tableau Rational
example_5_7 = IM.fromList
  [ (4, (IM.fromList [(1,-1), (2,-2), (3,-3)], -5))
  , (5, (IM.fromList [(1,-2), (2,-2), (3,-1)], -6))
  , (objRow, (IM.fromList [(1,3),(2,4),(3,5)], 0))
  ]

test_example_5_7 :: (Bool, Tableau Rational)
test_example_5_7 = dualSimplex OptMax example_5_7
-- optimal value should be -11

-- ---------------------------------------------------------------------------
