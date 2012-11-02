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

-- http://madscientist.jp/~ikegami/articles/IntroSequencePolynomial.html
-- optimum is (3,2,0)
test_ikegami = solve grlex cs obj
  where
    [x,y,z] = map LA.var [1..3]
    cs = [ 2.*.x .+. 2.*.y .+. 2.*.z .==. LA.constant 10
         , 3.*.x .+. y .+. z .==. LA.constant 11
         , x .>=. LA.constant 0
         , y .>=. LA.constant 0
         , z .>=. LA.constant 0
         ]
    obj = x .+. 2.*.y .+. 3.*.z

test_ikegami' = solve' grlex cs obj
  where
    [x,y,z] = [1..3]
    cs = [ (LA.fromTerms [(2,x),(2,y),(2,z)], 10)
         , (LA.fromTerms [(3,x),(1,y),(1,z)], 11)
         ]
    obj = LA.fromTerms [(1,x),(2,y),(3,z)]

-- http://posso.dm.unipi.it/users/traverso/conti-traverso-ip.ps
-- optimum is (39, 75, 1, 8, 122)
test_1 = solve grlex cs obj
  where
    vs@[x1,x2,x3,x4,x5] = map LA.var [1..5]
    cs = [ 2.*.x1 .+. 5.*.x2 .-. 3.*.x3 .+.     x4 .-. 2.*.x5 .==. LA.constant 214
         ,     x1 .+. 7.*.x2 .+. 2.*.x3 .+. 3.*.x4 .+.     x5 .==. LA.constant 712
         , 4.*.x1 .-. 2.*.x2 .-.     x3 .-. 5.*.x4 .+. 3.*.x5 .==. LA.constant 331
         ] ++
         [ v .>=. LA.constant 0 | v <- vs ]
    obj = x1 .+. x2 .+. x3 .+. x4 .+. x5

test_1' = solve' grlex cs obj
  where
    [x1,x2,x3,x4,x5] = [1..5]
    cs = [ (LA.fromTerms [(2, x1), ( 5, x2), (-3, x3), ( 1,x4), (-2, x5)], 214)
         , (LA.fromTerms [(1, x1), ( 7, x2), ( 2, x3), ( 3,x4), ( 1, x5)], 712)
         , (LA.fromTerms [(4, x1), (-2, x2), (-1, x3), (-5,x4), ( 3, x5)], 331)
         ]
    obj = LA.fromTerms [(1,x1),(1,x2),(1,x3),(1,x4),(1,x5)]

-- optimum is (0,2,2)
test_2 = solve grlex cs obj
  where
    vs@[x1,x2,x3] = map LA.var [1..3]
    cs = [ 2.*.x1 .+. 3.*.x2 .-. x3 .==. LA.constant 4 ] ++
         [ v .>=. LA.constant 0 | v <- vs ]
    obj = 2.*.x1 .+. x2

test_2' = solve' grlex cs obj
  where
    [x1,x2,x3] = [1..3]
    cs = [ (LA.fromTerms [(2, x1), (3, x2), (-1, x3)], 4) ]
    obj = LA.fromTerms [(2,x1),(1,x2)]

-- infeasible
test_3 = solve grlex cs obj
  where
    vs@[x1,x2,x3] = map LA.var [1..3]
    cs = [ 2.*.x1 .+. 2.*.x2 .+. 2.*.x3 .==. LA.constant 3 ] ++
         [ v .>=. LA.constant 0 | v <- vs ]
    obj = x1

test_3' = solve' grlex cs obj
  where
    [x1,x2,x3] = [1..3]
    cs = [ (LA.fromTerms [(2, x1), (2, x2), (2, x3)], 3) ]
    obj = LA.fromTerms [(1,x1)]
