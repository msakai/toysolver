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
import qualified Data.IntMultiSet as IMS

import qualified LA
import Expr (Variables (..))
import Polynomial

type Model = IM.IntMap Integer

solve :: MonomialOrder -> [Var] -> [(LA.Expr Integer, Integer)] -> LA.Expr Integer -> Maybe Model
solve cmp vs cs obj =
  if and [m IM.! y == 0 | y <- vs2]
    then Just $ IM.filterWithKey (\y _ -> y `IS.notMember` vs2') m
    else Nothing

  where
    v2 :: Var
    v2 = if null vs then 0 else maximum vs + 1

    vs2 :: [Var]
    vs2 = [v2 .. v2 + length cs - 1]

    vs2' = IS.fromList vs2

    cmp2 :: MonomialOrder
    cmp2 = elimOrdering (IS.fromList vs2) `mappend` costOrdering obj `mappend` cmp

    gbase = buchberger cmp2 $ do
      xj <- vs
      return (var xj - product [var yi ^ LA.coeff xj ai | ((ai,_),yi) <- zip cs vs2])

    yb = product [var yi ^ bi | ((_,bi),yi) <- zip cs vs2]

    [(_,z)] = terms (reduce cmp2 yb gbase)

    m = mkModel (vs++vs2) z

mkModel :: [Var] -> MonicMonomial -> Model
mkModel vs xs = IM.fromList [(x, fromIntegral (IMS.occur x xs)) | x <- vs]

costOrdering :: LA.Expr Integer -> MonomialOrder
costOrdering obj = \xs1 xs2 -> f xs1 `compare` f xs2
  where
    vs = vars obj
    f xs = LA.evalExpr (mkModel (IS.toList vs) xs) obj

elimOrdering :: IS.IntSet -> MonomialOrder
elimOrdering xs = compare `on` f
  where
    f ys = not (IS.null (xs `IS.intersection` IMS.toSet ys))

-- http://madscientist.jp/~ikegami/articles/IntroSequencePolynomial.html
test_ikegami = solve grlex vs cs obj
  where
    [x,y,z] = vs
    vs = [1..3]
    cs = [ (LA.fromTerms [(2,x),(2,y),(2,z)], 10)
         , (LA.fromTerms [(3,x),(1,y),(1,z)], 11)
         ]
    obj = LA.fromTerms [(1,x),(2,y),(3,z)]
