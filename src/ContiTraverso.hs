{-
http://posso.dm.unipi.it/users/traverso/conti-traverso-ip.ps
http://madscientist.jp/~ikegami/articles/IntroSequencePolynomial.html
http://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/1295-27.pdf
-}
module ContiTraverso
  ( solve
  , solve'
  ) where

import Data.Function
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Data.List
import Data.Monoid
import Data.Ratio

import Data.ArithRel
import Data.Linear
import qualified Data.LA as LA
import Data.Expr (Var, VarSet, Variables (..), Model)
import Data.Polynomial
import Data.Polynomial.GBase
import qualified LPUtil

solve :: MonomialOrder Var -> [LA.Atom Rational] -> LA.Expr Rational -> Maybe (Model Integer)
solve cmp cs obj = do
  m <- solve' cmp cs3 obj3
  return . IM.map round . mt . IM.map fromInteger $ m
  where
    ((obj2,cs2), mt) = LPUtil.toStandardForm (obj,cs)
    obj3 = LA.mapCoeff g obj2
      where
        g = round . (c*)
        c = fromInteger $ foldl' lcm 1 [denominator c | (c,_) <- LA.terms obj]
    cs3 = map f cs2
    f (lhs,rhs) = (LA.mapCoeff g lhs, g rhs)
      where
        g = round . (c*)
        c = fromInteger $ foldl' lcm 1 [denominator c | (c,_) <- LA.terms lhs]

solve' :: MonomialOrder Var -> [(LA.Expr Integer, Integer)] -> LA.Expr Integer -> Maybe (Model Integer)
solve' cmp cs obj = 
  if IM.keysSet (IM.filter (/= 0) m) `IS.isSubsetOf` vs'
    then Just $ IM.filterWithKey (\y _ -> y `IS.member` vs') m
    else Nothing

  where
    vs :: [Var]
    vs = IS.toList vs'

    vs' :: VarSet
    vs' = vars $ obj : [lhs | (lhs,_) <- cs]

    v2 :: Var
    v2 = if IS.null vs' then 0 else IS.findMax vs' + 1

    vs2 :: [Var]
    vs2 = [v2 .. v2 + length cs - 1]

    vs2' :: IS.IntSet
    vs2' = IS.fromList vs2

    t :: Var
    t = v2 + length cs

    cmp2 :: MonomialOrder Var
    cmp2 = elimOrdering (IS.fromList vs2) `mappend` elimOrdering (IS.singleton t) `mappend` costOrdering obj `mappend` cmp

    gbase :: [Polynomial Rational Var]
    gbase = buchberger cmp2 (product (map var (t:vs2)) - 1 : phi)
      where
        phi = do
          xj <- vs
          let aj = [(yi, aij) | (yi,(ai,_)) <- zip vs2 cs, let aij = LA.coeff xj ai]
          return $  product [var yi ^ aij    | (yi, aij) <- aj, aij > 0]
                  - product [var yi ^ (-aij) | (yi, aij) <- aj, aij < 0] * var xj

    yb = product [var yi ^ bi | ((_,bi),yi) <- zip cs vs2]

    [(_,z)] = terms (reduce cmp2 yb gbase)

    m = mkModel (vs++vs2++[t]) z

mkModel :: [Var] -> MonicMonomial Var -> Model Integer
mkModel vs xs = mmToIntMap xs `IM.union` IM.fromList [(x, 0) | x <- vs] 
-- IM.union is left-biased

costOrdering :: LA.Expr Integer -> MonomialOrder Var
costOrdering obj = compare `on` f
  where
    vs = vars obj
    f xs = LA.evalExpr (mkModel (IS.toList vs) xs) obj

elimOrdering :: IS.IntSet -> MonomialOrder Var
elimOrdering xs = compare `on` f
  where
    f ys = not (IS.null (xs `IS.intersection` IM.keysSet (mmToIntMap ys)))
