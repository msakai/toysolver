-----------------------------------------------------------------------------
-- |
-- Module      :  ToySolver.Arith.ContiTraverso
-- Copyright   :  (c) Masahiro Sakai 2012
-- License     :  BSD-style
-- 
-- Maintainer  :  masahiro.sakai@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
-- References:
--
-- * P. Conti and C. Traverso, "Buchberger algorithm and integer programming,"
--   Applied Algebra, Algebraic Algorithms and Error-Correcting Codes,
--   Lecture Notes in Computer Science Volume 539, 1991, pp 130-139
--   <http://dx.doi.org/10.1007/3-540-54522-0_102>
--   <http://posso.dm.unipi.it/users/traverso/conti-traverso-ip.ps>
--
-- * IKEGAMI Daisuke, "数列と多項式の愛しい関係," 2011,
--   <http://madscientist.jp/~ikegami/articles/IntroSequencePolynomial.html>
--
-- * 伊藤雅史, , 平林 隆一, "整数計画問題のための b-Gröbner 基底変換アルゴリズム,"
--   <http://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/1295-27.pdf>
-- 
--
-----------------------------------------------------------------------------
module ToySolver.Arith.ContiTraverso
  ( solve
  , solve'
  ) where

import Data.Default.Class
import Data.Function
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import qualified Data.Map as Map
import Data.List
import Data.Monoid
import Data.Ratio
import Data.VectorSpace

import Data.OptDir

import ToySolver.Data.ArithRel
import qualified ToySolver.Data.LA as LA
import ToySolver.Data.Polynomial (Polynomial, UPolynomial, Monomial, MonomialOrder)
import qualified ToySolver.Data.Polynomial as P
import ToySolver.Data.Polynomial.GroebnerBasis as GB
import ToySolver.Data.Var
import qualified ToySolver.Arith.LPUtil as LPUtil

solve :: MonomialOrder Var -> VarSet -> OptDir -> LA.Expr Rational -> [LA.Atom Rational] -> Maybe (Model Integer)
solve cmp vs dir obj cs = do
  m <- solve' cmp vs obj3 cs3
  return . IM.map round . mt . IM.map fromInteger $ m
  where
    ((obj2,cs2), mt) = LPUtil.toStandardForm (if dir == OptMin then obj else negateV obj, cs)
    obj3 = LA.mapCoeff g obj2
      where
        g = round . (c*)
        c = fromInteger $ foldl' lcm 1 [denominator c | (c,_) <- LA.terms obj]
    cs3 = map f cs2
    f (lhs,rhs) = (LA.mapCoeff g lhs, g rhs)
      where
        g = round . (c*)
        c = fromInteger $ foldl' lcm 1 [denominator c | (c,_) <- LA.terms lhs]

solve' :: MonomialOrder Var -> VarSet -> LA.Expr Integer -> [(LA.Expr Integer, Integer)] -> Maybe (Model Integer)
solve' cmp vs' obj cs
  | or [c < 0 | (c,x) <- LA.terms obj, x /= LA.unitVar] = error "all coefficient of cost function should be non-negative"
  | otherwise =
  if IM.keysSet (IM.filter (/= 0) m) `IS.isSubsetOf` vs'
    then Just $ IM.filterWithKey (\y _ -> y `IS.member` vs') m
    else Nothing

  where
    vs :: [Var]
    vs = IS.toList vs'

    v2 :: Var
    v2 = if IS.null vs' then 0 else IS.findMax vs' + 1

    vs2 :: [Var]
    vs2 = [v2 .. v2 + length cs - 1]

    t :: Var
    t = v2 + length cs

    cmp2 :: MonomialOrder Var
    cmp2 = elimOrdering (IS.fromList vs2) `mappend` elimOrdering (IS.singleton t) `mappend` costOrdering obj `mappend` cmp

    gb :: [Polynomial Rational Var]
    gb = GB.basis' def cmp2 (product (map P.var (t:vs2)) - 1 : phi)
      where
        phi = do
          xj <- vs
          let aj = [(yi, aij) | (yi,(ai,_)) <- zip vs2 cs, let aij = LA.coeff xj ai]
          return $  product [P.var yi ^ aij    | (yi, aij) <- aj, aij > 0]
                  - product [P.var yi ^ (-aij) | (yi, aij) <- aj, aij < 0] * P.var xj

    yb = product [P.var yi ^ bi | ((_,bi),yi) <- zip cs vs2]

    [(_,z)] = P.terms (P.reduce cmp2 yb gb)

    m = mkModel (vs++vs2++[t]) z

mkModel :: [Var] -> Monomial Var -> Model Integer
mkModel vs xs = IM.fromDistinctAscList (Map.toAscList (P.mindicesMap xs)) `IM.union` IM.fromList [(x, 0) | x <- vs]
-- IM.union is left-biased

costOrdering :: LA.Expr Integer -> MonomialOrder Var
costOrdering obj = compare `on` f
  where
    vs = vars obj
    f xs = LA.evalExpr (mkModel (IS.toList vs) xs) obj

elimOrdering :: IS.IntSet -> MonomialOrder Var
elimOrdering xs = compare `on` f
  where
    f ys = not $ IS.null $ xs `IS.intersection` ys'
      where
        ys' = IS.fromDistinctAscList [y | (y,_) <- Map.toAscList $ P.mindicesMap ys]
