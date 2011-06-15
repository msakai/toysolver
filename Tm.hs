-----------------------------------------------------------------------------
-- |
-- Module      :  Tm
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-----------------------------------------------------------------------------
module Tm where

import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Expr

infixl 6 .+., .-.

-- Linear combination of variables and constants.
-- Non-negative keys are used for variables's coefficients.
-- key '-1' is used for constants.
newtype Tm r = Tm{ unTm :: IM.IntMap r } deriving (Eq, Ord, Show)

instance Variables (Tm r) where
  vars (Tm m) = IS.delete constKey (IM.keysSet m)

constKey :: Int
constKey = -1

asConst :: Num r => Tm r -> Maybe r
asConst (Tm m) =
  case IM.toList m of
    [] -> Just 0
    [(v,x)] | v==constKey -> Just x
    _ -> Nothing

normalizeTm :: Num r => Tm r -> Tm r
normalizeTm (Tm t) = Tm $ IM.filter (0/=) t

varTm :: Num r => Var -> Tm r
varTm v = Tm $ IM.singleton v 1

constTm :: Num r => r -> Tm r
constTm c = normalizeTm $ Tm $ IM.singleton constKey c

(.+.) :: Num r => Tm r -> Tm r -> Tm r
Tm t1 .+. Tm t2 = normalizeTm $ Tm $ IM.unionWith (+) t1 t2

(.-.) :: Num r => Tm r -> Tm r -> Tm r
a .-. b = a .+. negateTm b

scaleTm :: Num r => r -> Tm r -> Tm r
scaleTm c (Tm t) = normalizeTm $ Tm $ IM.map (c*) t

negateTm :: Num r => Tm r -> Tm r
negateTm = scaleTm (-1)

evalTm :: Num r => Model r -> Tm r -> r
evalTm m (Tm t) = sum [(m' IM.! v) * c | (v,c) <- IM.toList t]
  where m' = IM.insert constKey 1 m

applySubst :: Num r => VarMap (Tm r) -> Tm r -> Tm r
applySubst s (Tm m) = foldr (.+.) (constTm 0) (map f (IM.toList m))
  where
    f (v,c) = scaleTm c $ 
      case IM.lookup v s of
        Just tm -> tm
        Nothing -> varTm v