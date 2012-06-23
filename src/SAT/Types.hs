{-# LANGUAGE BangPatterns #-}
module SAT.Types
  (
  -- * Variable
    Var
  , VarMap
  , validVar

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

  -- * Clause
  , Clause
  , normalizeClause

  -- * Cardinality Constraint
  , normalizeAtLeast

  -- * Pseudo Boolean Constraint
  , normalizePBAtLeast
  , normalizePBExactly
  , cutResolve
  , cardinalityReduction
  ) where

import Control.Monad
import Control.Exception
import Data.Ord
import Data.List
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import qualified Data.Set as Set

-- | Variable is represented as positive integers (DIMACS format).
type Var = Int

type VarMap = IM.IntMap

validVar :: Var -> Bool
validVar v = v > 0

-- | Positive (resp. negative) literals are represented as positive (resp.
-- negative) integers. (DIMACS format).
type Lit = Int

litUndef :: Lit
litUndef = 0

type LitSet = IS.IntSet
type LitMap = IM.IntMap

validLit :: Lit -> Bool
validLit l = l /= 0

-- | Construct a literal from a variable and its polarity.
-- 'True' (resp 'False') means positive (resp. negative) literal.
literal :: Var  -- ^ variable
        -> Bool -- ^ polarity
        -> Lit
literal v polarity =
  assert (validVar v) $ if polarity then v else litNot v

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

-- | Disjunction of 'Lit'.
type Clause = [Lit]

-- | Normalizing clause
--
-- 'Nothing' if the clause is trivially true.
normalizeClause :: Clause -> Maybe Clause
normalizeClause lits = assert (IS.size ys `mod` 2 == 0) $
  if IS.null ys
    then Just (IS.toList xs)
    else Nothing
  where
    xs = IS.fromList lits
    ys = xs `IS.intersection` (IS.map litNot xs)

normalizeAtLeast :: ([Lit],Int) -> ([Lit],Int)
normalizeAtLeast (lits,n) = assert (IS.size ys `mod` 2 == 0) $
   (IS.toList lits', n')
   where
     xs = IS.fromList lits
     ys = xs `IS.intersection` (IS.map litNot xs)
     lits' = xs `IS.difference` ys
     n' = n - (IS.size ys `div` 2)

-- | normalizing PB constraint of the form /c1 x1 + c2 cn ... cn xn >= b/.
normalizePBAtLeast :: ([(Integer,Lit)], Integer) -> ([(Integer,Lit)], Integer)
normalizePBAtLeast a =
　case step2 $ step1 $ a of
    (xs,n)
      | n > 0     -> step3 (saturate n xs, n)
      | otherwise -> ([], 0) -- trivially true
  where
    -- 同じ変数が複数回現れないように、一度全部 @v@ に統一。
    step1 :: ([(Integer,Lit)], Integer) -> ([(Integer,Lit)], Integer)
    step1 (xs,n) =
      case loop (IM.empty,n) xs of
        (ys,n') -> ([(c,v) | (v,c) <- IM.toList ys], n')
      where
        loop :: (VarMap Integer, Integer) -> [(Integer,Lit)] -> (VarMap Integer, Integer)
        loop (ys,m) [] = (ys,m)
        loop (ys,m) ((c,l):zs) =
          if litPolarity l
            then loop (IM.insertWith (+) l c ys, m) zs
            else loop (IM.insertWith (+) (litNot l) (negate c) ys, m-c) zs

    -- 係数が0のものも取り除き、係数が負のリテラルを反転することで、
    -- 係数が正になるようにする。
    step2 :: ([(Integer,Lit)], Integer) -> ([(Integer,Lit)], Integer)
    step2 (xs,n) = loop ([],n) xs
      where
        loop (ys,m) [] = (ys,m)
        loop (ys,m) (t@(c,l):zs)
          | c == 0 = loop (ys,m) zs
          | c < 0  = loop ((negate c,litNot l):ys, m-c) zs
          | otherwise = loop (t:ys,m) zs

    -- degree以上の係数はそこで抑える。
    saturate :: Integer -> [(Integer,Lit)] -> [(Integer,Lit)]
    saturate n xs = [assert (c>0) (min n c, l) | (c,l) <- xs]

    -- omega test と同様の係数の gcd による単純化
    step3 :: ([(Integer,Lit)], Integer) -> ([(Integer,Lit)], Integer)
    step3 ([],n) = ([],n)
    step3 (xs,n) = ([(c `div` d, l) | (c,l) <- xs], (n+d-1) `div` d)
      where
        d = foldl1' gcd [c | (c,_) <- xs]

-- | normalizing PB constraint of the form /c1 x1 + c2 cn ... cn xn = b/.
normalizePBExactly :: ([(Integer,Lit)], Integer) -> ([(Integer,Lit)], Integer)
normalizePBExactly a =
　case step2 $ step1 $ a of
    (xs,n)
      | n >= 0    -> step3 (xs, n)
      | otherwise -> ([], 1) -- false
  where
    -- 同じ変数が複数回現れないように、一度全部 @v@ に統一。
    step1 :: ([(Integer,Lit)], Integer) -> ([(Integer,Lit)], Integer)
    step1 (xs,n) =
      case loop (IM.empty,n) xs of
        (ys,n') -> ([(c,v) | (v,c) <- IM.toList ys], n')
      where
        loop :: (VarMap Integer, Integer) -> [(Integer,Lit)] -> (VarMap Integer, Integer)
        loop (ys,m) [] = (ys,m)
        loop (ys,m) ((c,l):zs) =
          if litPolarity l
            then loop (IM.insertWith (+) l c ys, m) zs
            else loop (IM.insertWith (+) (litNot l) (negate c) ys, m-c) zs

    -- 係数が0のものも取り除き、係数が負のリテラルを反転することで、
    -- 係数が正になるようにする。
    step2 :: ([(Integer,Lit)], Integer) -> ([(Integer,Lit)], Integer)
    step2 (xs,n) = loop ([],n) xs
      where
        loop (ys,m) [] = (ys,m)
        loop (ys,m) (t@(c,l):zs)
          | c == 0 = loop (ys,m) zs
          | c < 0  = loop ((negate c,litNot l):ys, m-c) zs
          | otherwise = loop (t:ys,m) zs

    -- omega test と同様の係数の gcd による単純化
    step3 :: ([(Integer,Lit)], Integer) -> ([(Integer,Lit)], Integer)
    step3 ([],n) = ([],n)
    step3 (xs,n)
      | n `mod` d == 0 = ([(c `div` d, l) | (c,l) <- xs], n `div` d)
      | otherwise      = ([], 1) -- false
      where
        d = foldl1' gcd [c | (c,_) <- xs]

cutResolve :: ([(Integer,Lit)],Integer) -> ([(Integer,Lit)],Integer) -> Var -> ([(Integer,Lit)],Integer)
cutResolve (lhs1,rhs1) (lhs2,rhs2) v = assert (l1 == litNot l2) $ normalizePBAtLeast pb
  where
    (c1,l1) = head [(c,l) | (c,l) <- lhs1, litVar l == v]
    (c2,l2) = head [(c,l) | (c,l) <- lhs2, litVar l == v]
    g = gcd c1 c2
    s1 = c2 `div` g
    s2 = c1 `div` g
    pb = ([(s1*c,l) | (c,l) <- lhs1] ++ [(s2*c,l) | (c,l) <- lhs2], s1*rhs1 + s2 * rhs2)

cardinalityReduction :: ([(Integer,Lit)],Integer) -> ([Lit],Int)
cardinalityReduction (lhs,rhs) = (ls, rhs')
  where
    rhs' = go1 0 0 (sortBy (flip (comparing fst)) lhs)

    go1 !s !k ((a,_):ts)
      | s < rhs   = go1 (s+a) (k+1) ts
      | otherwise = k
    go1 _ _ [] = error "cardinalityReduction: should not happen"

    ls = go2 (minimum (rhs : map (subtract 1 . fst) lhs)) (sortBy (comparing fst) lhs)

    go2 !guard' ((a,_) : ts)
      | a - 1 < guard' = go2 (guard' - a) ts
      | otherwise      = map snd ts
    go2 _ [] = error "cardinalityReduction: should not happen"
