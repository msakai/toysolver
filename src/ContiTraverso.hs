{-
http://posso.dm.unipi.it/users/traverso/conti-traverso-ip.ps
http://madscientist.jp/~ikegami/articles/IntroSequencePolynomial.html
http://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/1295-27.pdf
-}
module ContiTraverso where

import Data.Function
import Data.Monoid
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS

import qualified LA
import Expr (Variables (..))
import Polynomial

type Model = IM.IntMap Integer

solve :: MonomialOrder -> [Var] -> [(LA.Expr Integer, Integer)] -> LA.Expr Integer -> Maybe Model
solve cmp vs cs obj = 
  if IM.keysSet (IM.filter (/= 0) m) `IS.isSubsetOf` vs'
    then Just $ IM.filterWithKey (\y _ -> y `IS.member` vs') m
    else Nothing

  where
    vs' :: IS.IntSet
    vs' = IS.fromList vs

    v2 :: Var
    v2 = if null vs then 0 else maximum vs + 1

    vs2 :: [Var]
    vs2 = [v2 .. v2 + length cs - 1]

    vs2' :: IS.IntSet
    vs2' = IS.fromList vs2

    t :: Var
    t = v2 + length cs

    cmp2 :: MonomialOrder
    cmp2 = elimOrdering (IS.fromList vs2) `mappend` elimOrdering (IS.singleton t) `mappend` costOrdering obj `mappend` cmp

    gbase :: [Polynomial Rational]
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

mkModel :: [Var] -> MonicMonomial -> Model
mkModel vs xs = mmToIntMap xs `IM.union` IM.fromList [(x, 0) | x <- vs] 
-- IM.union is left-biased

costOrdering :: LA.Expr Integer -> MonomialOrder
costOrdering obj = compare `on` f
  where
    vs = vars obj
    f xs = LA.evalExpr (mkModel (IS.toList vs) xs) obj

elimOrdering :: IS.IntSet -> MonomialOrder
elimOrdering xs = compare `on` f
  where
    f ys = not (IS.null (xs `IS.intersection` IM.keysSet (mmToIntMap ys)))

-- http://madscientist.jp/~ikegami/articles/IntroSequencePolynomial.html
-- optimum is (3,2,0)
test_ikegami = solve grlex vs cs obj
  where
    [x,y,z] = vs
    vs = [1..3]
    cs = [ (LA.fromTerms [(2,x),(2,y),(2,z)], 10)
         , (LA.fromTerms [(3,x),(1,y),(1,z)], 11)
         ]
    obj = LA.fromTerms [(1,x),(2,y),(3,z)]

-- http://posso.dm.unipi.it/users/traverso/conti-traverso-ip.ps
-- optimum is (39, 75, 1, 8, 122)
test_1 = solve grlex vs cs obj
  where
    [x1,x2,x3,x4,x5] = vs
    vs = [1..5]
    cs = [ (LA.fromTerms [(2, x1), ( 5, x2), (-3, x3), ( 1,x4), (-2, x5)], 214)
         , (LA.fromTerms [(1, x1), ( 7, x2), ( 2, x3), ( 3,x4), ( 1, x5)], 712)
         , (LA.fromTerms [(4, x1), (-2, x2), (-1, x3), (-5,x4), ( 3, x5)], 331)
         ]
    obj = LA.fromTerms [(1,x1),(1,x2),(1,x3),(1,x4),(1,x5)]

-- optimum is (0,2,2)
test_2 = solve grlex vs cs obj
  where
    [x1,x2,x3] = vs
    vs = [1..3]
    cs = [ (LA.fromTerms [(2, x1), (3, x2), (-1, x3)], 4) ]
    obj = LA.fromTerms [(2,x1),(1,x2)]

-- infeasible
test_3 = solve grlex vs cs obj
  where
    [x1,x2,x3] = vs
    vs = [1..3]
    cs = [ (LA.fromTerms [(2, x1), (2, x2), (2, x3)], 3) ]
    obj = LA.fromTerms [(1,x1)]
