{-# LANGUAGE ScopedTypeVariables, BangPatterns, FlexibleInstances #-}
module ToySolver.SAT.Types
  (
  -- * Variable
    Var
  , VarSet
  , VarMap
  , validVar

  -- * Model
  , IModel (..)
  , Model

  -- * Literal
  , Lit
  , LitSet
  , LitMap
  , litUndef
  , validLit
  , literal
  , litNot
  , litVar
  , litPolarity
  , evalLit

  -- * Clause
  , Clause
  , normalizeClause
  , instantiateClause
  , clauseSubsume
  , evalClause
  , clauseToPBLinAtLeast

  -- * Cardinality Constraint
  , AtLeast
  , normalizeAtLeast
  , instantiateAtLeast
  , evalAtLeast

  -- * Pseudo Boolean Constraint
  , PBLinTerm
  , PBLinSum
  , PBLinAtLeast
  , PBLinExactly
  , normalizePBLinSum
  , normalizePBLinAtLeast
  , normalizePBLinExactly
  , instantiatePBLinAtLeast
  , instantiatePBLinExactly
  , cutResolve
  , cardinalityReduction
  , negatePBLinAtLeast
  , evalPBLinSum
  , evalPBLinAtLeast
  , evalPBLinExactly
  , pbLowerBound
  , pbUpperBound
  , pbSubsume

  -- * XOR Clause
  , XORClause
  , normalizeXORClause
  , instantiateXORClause
  , evalXORClause
  ) where

import Control.Monad
import Control.Exception
import Data.Array.Unboxed
import Data.Ord
import Data.List
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import ToySolver.Data.LBool

-- | Variable is represented as positive integers (DIMACS format).
type Var = Int

type VarSet = IntSet
type VarMap = IntMap

{-# INLINE validVar #-}
validVar :: Var -> Bool
validVar v = v > 0

class IModel a where
  evalVar :: a -> Var -> Bool

-- | A model is represented as a mapping from variables to its values.
type Model = UArray Var Bool

instance IModel (UArray Var Bool) where
  evalVar m v = m ! v

instance IModel (Array Var Bool) where
  evalVar m v = m ! v

instance IModel (Var -> Bool) where
  evalVar m v = m v

-- | Positive (resp. negative) literals are represented as positive (resp.
-- negative) integers. (DIMACS format).
type Lit = Int

{-# INLINE litUndef #-}
litUndef :: Lit
litUndef = 0

type LitSet = IntSet
type LitMap = IntMap

{-# INLINE validLit #-}
validLit :: Lit -> Bool
validLit l = l /= 0

{-# INLINE literal #-}
-- | Construct a literal from a variable and its polarity.
-- 'True' (resp 'False') means positive (resp. negative) literal.
literal :: Var  -- ^ variable
        -> Bool -- ^ polarity
        -> Lit
literal v polarity =
  assert (validVar v) $ if polarity then v else litNot v

{-# INLINE litNot #-}
-- | Negation of the 'Lit'.
litNot :: Lit -> Lit
litNot l = assert (validLit l) $ negate l

{-# INLINE litVar #-}
-- | Underlying variable of the 'Lit'
litVar :: Lit -> Var
litVar l = assert (validLit l) $ abs l

{-# INLINE litPolarity #-}
-- | Polarity of the 'Lit'.
-- 'True' means positive literal and 'False' means negative literal.
litPolarity :: Lit -> Bool
litPolarity l = assert (validLit l) $ l > 0

{-# INLINEABLE evalLit #-}
{-# SPECIALIZE evalLit :: Model -> Lit -> Bool #-}
evalLit :: IModel m => m -> Lit -> Bool
evalLit m l = if l > 0 then evalVar m l else not (evalVar m (abs l))

-- | Disjunction of 'Lit'.
type Clause = [Lit]

-- | Normalizing clause
--
-- 'Nothing' if the clause is trivially true.
normalizeClause :: Clause -> Maybe Clause
normalizeClause lits = assert (IntSet.size ys `mod` 2 == 0) $
  if IntSet.null ys
    then Just (IntSet.toList xs)
    else Nothing
  where
    xs = IntSet.fromList lits
    ys = xs `IntSet.intersection` (IntSet.map litNot xs)

{-# SPECIALIZE instantiateClause :: (Lit -> IO LBool) -> Clause -> IO (Maybe Clause) #-}
instantiateClause :: forall m. Monad m => (Lit -> m LBool) -> Clause -> m (Maybe Clause)
instantiateClause evalLitM = loop []
  where
    loop :: [Lit] -> [Lit] -> m (Maybe Clause)
    loop ret [] = return $ Just ret
    loop ret (l:ls) = do
      val <- evalLitM l
      if val==lTrue then
        return Nothing
      else if val==lFalse then
        loop ret ls
      else
        loop (l : ret) ls

clauseSubsume :: Clause -> Clause -> Bool
clauseSubsume cl1 cl2 = cl1' `IntSet.isSubsetOf` cl2'
  where
    cl1' = IntSet.fromList cl1
    cl2' = IntSet.fromList cl2

evalClause :: IModel m => m -> Clause -> Bool
evalClause m cl = any (evalLit m) cl

clauseToPBLinAtLeast :: Clause -> PBLinAtLeast
clauseToPBLinAtLeast xs = ([(1,l) | l <- xs], 1)

type AtLeast = ([Lit], Int)

normalizeAtLeast :: AtLeast -> AtLeast
normalizeAtLeast (lits,n) = assert (IntSet.size ys `mod` 2 == 0) $
   (IntSet.toList lits', n')
   where
     xs = IntSet.fromList lits
     ys = xs `IntSet.intersection` (IntSet.map litNot xs)
     lits' = xs `IntSet.difference` ys
     n' = n - (IntSet.size ys `div` 2)

{-# SPECIALIZE instantiateAtLeast :: (Lit -> IO LBool) -> AtLeast -> IO AtLeast #-}
instantiateAtLeast :: forall m. Monad m => (Lit -> m LBool) -> AtLeast -> m AtLeast
instantiateAtLeast evalLitM (xs,n) = loop ([],n) xs
  where
    loop :: AtLeast -> [Lit] -> m AtLeast
    loop ret [] = return ret
    loop (ys,m) (l:ls) = do
      val <- evalLitM l
      if val == lTrue then
        loop (ys, m-1) ls
      else if val == lFalse then
        loop (ys, m) ls
      else
        loop (l:ys, m) ls

evalAtLeast :: IModel m => m -> AtLeast -> Bool
evalAtLeast m (lits,n) = sum [1 | lit <- lits, evalLit m lit] >= n

type PBLinTerm = (Integer, Lit)
type PBLinSum = [PBLinTerm]
type PBLinAtLeast = (PBLinSum, Integer)
type PBLinExactly = (PBLinSum, Integer)

-- | normalizing PB term of the form /c1 x1 + c2 x2 ... cn xn + c/ into
-- /d1 x1 + d2 x2 ... dm xm + d/ where d1,...,dm ≥ 1.
normalizePBLinSum :: (PBLinSum, Integer) -> (PBLinSum, Integer)
normalizePBLinSum = step2 . step1
  where
    -- 同じ変数が複数回現れないように、一度全部 @v@ に統一。
    step1 :: (PBLinSum, Integer) -> (PBLinSum, Integer)
    step1 (xs,n) =
      case loop (IntMap.empty,n) xs of
        (ys,n') -> ([(c,v) | (v,c) <- IntMap.toList ys], n')
      where
        loop :: (VarMap Integer, Integer) -> PBLinSum -> (VarMap Integer, Integer)
        loop (ys,m) [] = (ys,m)
        loop (ys,m) ((c,l):zs) =
          if litPolarity l
            then loop (IntMap.insertWith (+) l c ys, m) zs
            else loop (IntMap.insertWith (+) (litNot l) (negate c) ys, m+c) zs

    -- 係数が0のものも取り除き、係数が負のリテラルを反転することで、
    -- 係数が正になるようにする。
    step2 :: (PBLinSum, Integer) -> (PBLinSum, Integer)
    step2 (xs,n) = loop ([],n) xs
      where
        loop (ys,m) [] = (ys,m)
        loop (ys,m) (t@(c,l):zs)
          | c == 0 = loop (ys,m) zs
          | c < 0  = loop ((negate c,litNot l):ys, m+c) zs
          | otherwise = loop (t:ys,m) zs

-- | normalizing PB constraint of the form /c1 x1 + c2 cn ... cn xn >= b/.
normalizePBLinAtLeast :: PBLinAtLeast -> PBLinAtLeast
normalizePBLinAtLeast a =
  case step1 a of
    (xs,n)
      | n > 0     -> step3 (saturate n xs, n)
      | otherwise -> ([], 0) -- trivially true
  where
    step1 :: PBLinAtLeast -> PBLinAtLeast
    step1 (xs,n) =
      case normalizePBLinSum (xs,-n) of
        (ys,m) -> (ys, -m)

    -- degree以上の係数はそこで抑える。
    saturate :: Integer -> PBLinSum -> PBLinSum
    saturate n xs = [assert (c>0) (min n c, l) | (c,l) <- xs]

    -- omega test と同様の係数の gcd による単純化
    step3 :: PBLinAtLeast -> PBLinAtLeast
    step3 ([],n) = ([],n)
    step3 (xs,n) = ([(c `div` d, l) | (c,l) <- xs], (n+d-1) `div` d)
      where
        d = foldl1' gcd [c | (c,_) <- xs]

-- | normalizing PB constraint of the form /c1 x1 + c2 cn ... cn xn = b/.
normalizePBLinExactly :: PBLinExactly -> PBLinExactly
normalizePBLinExactly a =
　case step1 $ a of
    (xs,n)
      | n >= 0    -> step2 (xs, n)
      | otherwise -> ([], 1) -- false
  where
    step1 :: PBLinExactly -> PBLinExactly
    step1 (xs,n) =
      case normalizePBLinSum (xs,-n) of
        (ys,m) -> (ys, -m)

    -- omega test と同様の係数の gcd による単純化
    step2 :: PBLinExactly -> PBLinExactly
    step2 ([],n) = ([],n)
    step2 (xs,n)
      | n `mod` d == 0 = ([(c `div` d, l) | (c,l) <- xs], n `div` d)
      | otherwise      = ([], 1) -- false
      where
        d = foldl1' gcd [c | (c,_) <- xs]

{-# SPECIALIZE instantiatePBLinAtLeast :: (Lit -> IO LBool) -> PBLinAtLeast -> IO PBLinAtLeast #-}
instantiatePBLinAtLeast :: forall m. Monad m => (Lit -> m LBool) -> PBLinAtLeast -> m PBLinAtLeast
instantiatePBLinAtLeast evalLitM (xs,n) = loop ([],n) xs
  where
    loop :: PBLinAtLeast -> PBLinSum -> m PBLinAtLeast
    loop ret [] = return ret
    loop (ys,m) ((c,l):ts) = do
      val <- evalLitM l
      if val == lTrue then
        loop (ys, m-c) ts
      else if val == lFalse then
        loop (ys, m) ts
      else
        loop ((c,l):ys, m) ts

{-# SPECIALIZE instantiatePBLinExactly :: (Lit -> IO LBool) -> PBLinExactly -> IO PBLinExactly #-}
instantiatePBLinExactly :: Monad m => (Lit -> m LBool) -> PBLinExactly -> m PBLinExactly
instantiatePBLinExactly = instantiatePBLinAtLeast

cutResolve :: PBLinAtLeast -> PBLinAtLeast -> Var -> PBLinAtLeast
cutResolve (lhs1,rhs1) (lhs2,rhs2) v = assert (l1 == litNot l2) $ normalizePBLinAtLeast pb
  where
    (c1,l1) = head [(c,l) | (c,l) <- lhs1, litVar l == v]
    (c2,l2) = head [(c,l) | (c,l) <- lhs2, litVar l == v]
    g = gcd c1 c2
    s1 = c2 `div` g
    s2 = c1 `div` g
    pb = ([(s1*c,l) | (c,l) <- lhs1] ++ [(s2*c,l) | (c,l) <- lhs2], s1*rhs1 + s2 * rhs2)

cardinalityReduction :: PBLinAtLeast -> AtLeast
cardinalityReduction (lhs,rhs) = (ls, rhs')
  where
    rhs' = go1 0 0 (sortBy (flip (comparing fst)) lhs)

    go1 !s !k ((a,_):ts)
      | s < rhs   = go1 (s+a) (k+1) ts
      | otherwise = k
    go1 _ _ [] = error "ToySolver.SAT.Types.cardinalityReduction: should not happen"

    ls = go2 (minimum (rhs : map (subtract 1 . fst) lhs)) (sortBy (comparing fst) lhs)

    go2 !guard' ((a,_) : ts)
      | a - 1 < guard' = go2 (guard' - a) ts
      | otherwise      = map snd ts
    go2 _ [] = error "ToySolver.SAT.Types.cardinalityReduction: should not happen"

negatePBLinAtLeast :: PBLinAtLeast -> PBLinAtLeast
negatePBLinAtLeast (xs, rhs) = ([(-c,lit) | (c,lit)<-xs] , -rhs + 1)

evalPBLinSum :: IModel m => m -> PBLinSum -> Integer
evalPBLinSum m xs = sum [c | (c,lit) <- xs, evalLit m lit]

evalPBLinAtLeast :: IModel m => m -> PBLinAtLeast -> Bool
evalPBLinAtLeast m (lhs,rhs) = evalPBLinSum m lhs >= rhs

evalPBLinExactly :: IModel m => m -> PBLinAtLeast -> Bool
evalPBLinExactly m (lhs,rhs) = evalPBLinSum m lhs == rhs

pbLowerBound :: PBLinSum -> Integer
pbLowerBound xs = sum [if c < 0 then c else 0 | (c,_) <- xs]

pbUpperBound :: PBLinSum -> Integer
pbUpperBound xs = sum [if c > 0 then c else 0 | (c,_) <- xs]

-- (Σi ci li ≥ rhs1) subsumes (Σi di li ≥ rhs2) iff rhs1≥rhs2 and di≥ci for all i.
pbSubsume :: PBLinAtLeast -> PBLinAtLeast -> Bool
pbSubsume (lhs1,rhs1) (lhs2,rhs2) =
  rhs1 >= rhs2 && and [di >= ci | (ci,li) <- lhs1, let di = IntMap.findWithDefault 0 li lhs2']
  where
    lhs2' = IntMap.fromList [(l,c) | (c,l) <- lhs2]


-- | XOR clause
--
-- '([l1,l2..ln], b)' means l1 ⊕ l2 ⊕ ⋯ ⊕ ln = b.
--
-- Note that:
--
-- * True can be represented as ([], False)
--
-- * False can be represented as ([], True)
--
type XORClause = ([Lit], Bool)

-- | Normalize XOR clause
normalizeXORClause :: XORClause -> XORClause
normalizeXORClause (lits, b) =
  case IntMap.keys m of
    0:xs -> (xs, not b)
    xs -> (xs, b)
  where
    m = IntMap.filter id $ IntMap.unionsWith xor [f lit | lit <- lits]
    xor = (/=)

    f 0 = IntMap.singleton 0 True
    f lit =
      if litPolarity lit
      then IntMap.singleton lit True
      else IntMap.fromList [(litVar lit, True), (0, True)]  -- ¬x = x ⊕ 1

{-# SPECIALIZE instantiateXORClause :: (Lit -> IO LBool) -> XORClause -> IO XORClause #-}
instantiateXORClause :: forall m. Monad m => (Lit -> m LBool) -> XORClause -> m XORClause
instantiateXORClause evalLitM (ls,b) = loop [] b ls
  where
    loop :: [Lit] -> Bool -> [Lit] -> m XORClause
    loop lhs !rhs [] = return (lhs, rhs)
    loop lhs !rhs (l:ls) = do
      val <- evalLitM l
      if val==lTrue then
        loop lhs (not rhs) ls
      else if val==lFalse then
        loop lhs rhs ls
      else
        loop (l : lhs) rhs ls

evalXORClause :: IModel m => m -> XORClause -> Bool
evalXORClause m (lits, rhs) = foldl' xor False (map f lits) == rhs
  where
    xor = (/=)
    f 0 = True
    f lit = evalLit m lit
