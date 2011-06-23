-----------------------------------------------------------------------------
-- |
-- Module      :  LC
-- Copyright   :  (c) Masahiro Sakai 2011
-- License     :  BSD-style
-- 
-----------------------------------------------------------------------------
module LC where

import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Expr

infixl 6 .+., .-.

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

(.+.) :: Num r => LC r -> LC r -> LC r
LC t1 .+. LC t2 = normalizeLC $ LC $ IM.unionWith (+) t1 t2

(.-.) :: Num r => LC r -> LC r -> LC r
a .-. b = a .+. negateLC b

scaleLC :: Num r => r -> LC r -> LC r
scaleLC c (LC t) = normalizeLC $ LC $ IM.map (c*) t

negateLC :: Num r => LC r -> LC r
negateLC = scaleLC (-1)

evalLC :: Num r => Model r -> LC r -> r
evalLC m (LC t) = sum [(m' IM.! v) * c | (v,c) <- IM.toList t]
  where m' = IM.insert constKey 1 m

applySubst :: Num r => VarMap (LC r) -> LC r -> LC r
applySubst s (LC m) = foldr (.+.) (constLC 0) (map f (IM.toList m))
  where
    f (v,c) = scaleLC c $ 
      case IM.lookup v s of
        Just tm -> tm
        Nothing -> varLC v

fvLC :: LC r -> VarSet
fvLC (LC m) = IS.fromAscList [v | (v,_) <- IM.toAscList m, v /= constKey]
