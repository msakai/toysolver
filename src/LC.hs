-----------------------------------------------------------------------------
-- |
-- Module      :  LC
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-----------------------------------------------------------------------------
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
module LC
  ( module Linear
  , LC (..)
  , constKey
  , asConst
  , normalizeLC
  , varLC
  , constLC
  , mapLC
  , evalLC
  , lift1LC
  , applySubst
  , applySubst1
  , fvLC
  , pickupLC
  ) where

import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Linear
import Expr

-- Linear combination of variables and constants.
-- Non-negative keys are used for variables's coefficients.
-- key '-1' is used for constants.
newtype LC r = LC{ unLC :: IM.IntMap r } deriving (Eq, Ord, Show)

instance Variables (LC r) where
  vars (LC m) = IS.delete constKey (IM.keysSet m)

constKey :: Int
constKey = -1

asConst :: Num r => LC r -> Maybe r
asConst (LC m) =
  case IM.toList m of
    [] -> Just 0
    [(v,x)] | v==constKey -> Just x
    _ -> Nothing

normalizeLC :: Num r => LC r -> LC r
normalizeLC (LC t) = LC $ IM.filter (0/=) t

varLC :: Num r => Var -> LC r
varLC v = LC $ IM.singleton v 1

constLC :: Num r => r -> LC r
constLC c = normalizeLC $ LC $ IM.singleton constKey c

mapLC :: Num b => (a -> b) -> LC a -> LC b
mapLC f (LC t) = normalizeLC $ LC $ IM.map f t

instance Num r => Linear r (LC r) where
  LC t1 .+. LC t2 = normalizeLC $ LC $ IM.unionWith (+) t1 t2
  c .*. (LC t) = normalizeLC $ LC $ IM.map (c*) t
  lzero = LC $ IM.empty

evalLC :: Num r => Model r -> LC r -> r
evalLC m (LC t) = sum [(m' IM.! v) * c | (v,c) <- IM.toList t]
  where m' = IM.insert constKey 1 m

lift1LC :: Linear r x => x -> (Var -> x) -> LC r -> x
lift1LC unit f (LC t) = lsum [c .*. (g v) | (v,c) <- IM.toList t]
  where
    g v
      | v==constKey = unit
      | otherwise   = f v

applySubst :: Num r => VarMap (LC r) -> LC r -> LC r
applySubst s (LC m) = lsum (map f (IM.toList m))
  where
    f (v,c) = c .*. (
      case IM.lookup v s of
        Just tm -> tm
        Nothing -> varLC v)

applySubst1 :: Num r => Var -> LC r -> LC r -> LC r
applySubst1 x lc lc1@(LC m) = 
  case IM.lookup x m of
    Nothing -> lc1
    Just c -> c .*. lc .+. LC (IM.delete x m)

fvLC :: LC r -> VarSet
fvLC (LC m) = IS.fromAscList [v | (v,_) <- IM.toAscList m, v /= constKey]

pickupLC :: Num r => Var -> LC r -> (r, LC r)
pickupLC v (LC m) = (IM.findWithDefault 0 v m, LC (IM.delete v m))
